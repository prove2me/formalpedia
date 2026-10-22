-- Prove2me | Theorems.Thm_SuperBAE_Restriction_reduced_system
-- name    : SuperBAE.Restriction.reduced_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:28.418001+00:00
-- url     : https://prove2.me/theorems/40ed4cc6-f1f4-499e-aba0-83cbf4d70f5b
-- title:
--   §4.1, p. 18 (PDF 19) — the restricted system is the gl(M−1|N−1) BAE for Δ₀^{M−1|N−1} = {α_1, …, α_{k−2}, ε_{k−1} − ε_{k+2}, α_{k+2}, …, α_r}
-- statement:
--   In the setting of the $\mathfrak{gl}(M|N)$ Bethe ansatz equations (2.9) with $n=M-N>0$, let $\alpha_k$ satisfy **A1** ($\sigma_k\sigma_{k+1}=-1$) and **A2** ($2\le k\le d-2$), and assume **R1** (the roots of types $k-1$ and $k+1$ coincide). Delete grading positions $k,k+1$ and root types $k,k+1$; call the result the reduced grading $\sigma'$ on $d-2$ positions and the reduced root family. Then:
--
--   1. the reduced grading has $M-1$ even and $N-1$ odd positions, and the same loop weight: $n' = n$;
--   2. for every root $u$ of type $k-1$, the reduced Bethe equation of type $k-1$ (whose simple root is $\epsilon_{k-1}-\epsilon_{k+2}$) at $u$ is equivalent to (4.6) at $u$;
--   3. for every other reduced type $i\in\{1,\dots,d-3\}$, $i\neq k-1$, and every $u\in\mathbb{C}$, the reduced Bethe equation of type $i$ at $u$ is the original equation (2.9) of type $i$ if $i<k$, and of type $i+2$ if $i\ge k$.
--
--   So the restricted equations are precisely the Bethe ansatz equations of the $\mathfrak{gl}(M-1|N-1)$ chain for the simple root system $\Delta^{M-1|N-1}_0=\{\alpha_1,\dots,\alpha_{k-2},\epsilon_{k-1}-\epsilon_{k+2},\alpha_{k+2},\dots,\alpha_r\}$.
--
--   **Formalization Note.** The reduced system is the same Bethe predicate applied to the deleted grading on $d-2$ positions and the reindexed roots, with its own source terms $\Lambda'_i$ and its own loop weight $n'$; item 1 shows $n'=n$. Item 3 at $i=k$ uses R1, since the left neighbour of old type $k+2$ becomes type $k-1$. The paper phrases the reduction through (2.10) and cohomological reduction; the statement here is its content at the level of the equations (2.9). The standing assumption $N<M$ (p. 7) is kept; it is not used.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, p. 18 (PDF 19), §4.1, "The reduced BAE have the form (2.10) corresponding to precisely the simple root system Δ_0^{M−1|N−1}"; §4.2 p. 18 (PDF 19)

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace SuperBAE.Restriction

theorem reduced_system (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hR1 : roots (k - 1) = roots (k + 1)) :
    (numEven (delGrading k odd) (d - 2) = numEven odd d - 1 ∧
        numOdd (delGrading k odd) (d - 2) = numOdd odd d - 1 ∧
        nLoop (delGrading k odd) (d - 2) = nLoop odd d) ∧
      (∀ u ∈ roots (k - 1),
        bae L (delGrading k odd) (d - 2) (delRoots k roots) (k - 1) u ↔
          eq4_6 L odd d roots k u) ∧
      (∀ i ∈ Finset.Icc 1 (d - 3), i ≠ k - 1 → ∀ u : ℂ,
        bae L (delGrading k odd) (d - 2) (delRoots k roots) i u ↔
          bae L odd d roots (if i < k then i else i + 2) u) := by sorry

end SuperBAE.Restriction
