-- Prove2me | Theorems.Thm_SuperBAE_Restriction_bae_restriction
-- name    : SuperBAE.Restriction.bae_restriction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:29.329653+00:00
-- url     : https://prove2.me/theorems/0c0389f7-d2b3-4183-a8ad-a196d8fc87ef
-- title:
--   §4.1–4.2, pp. 17–19 (PDF 18–20) — odd sourceless α_k, R1: gl(M|N) BAE ⇔ gl(M−1|N−1) BAE ∧ (4.2), and equal energy (2.18)
-- statement:
--   Consider the homogeneous $\mathfrak{gl}(M|N)$ spin chain $(V\otimes V^*)^{\otimes L}$ in a grading $\sigma_1,\dots,\sigma_d$, $d=M+N$, with loop weight $n=M-N>0$, and a family of Bethe roots $\{u^{(l)}_j\}$, $l=1,\dots,r=d-1$. Fix a simple root $\alpha_k$ with
--
--   1. **A1** $\alpha_k$ odd: $\sigma_k\sigma_{k+1}=-1$;
--   2. **A2** $\alpha_k$ without source terms: $2\le k\le d-2$ (i.e. $k\ne 1,r$);
--   3. **R1** the roots of types $k-1$ and $k+1$ coincide: $\{u^{(k-1)}_j\}=\{u^{(k+1)}_j\}$;
--
--   and suppose the root family is regular. Let the reduced data be obtained by deleting grading positions $k,k+1$ and root types $k,k+1$. Then
--
--   $$\Big(\text{the roots solve the }\mathfrak{gl}(M|N)\text{ BAE (2.9)}\Big) \iff \Big(\text{the reduced roots solve the }\mathfrak{gl}(M-1|N-1)\text{ BAE} \;\wedge\; (2.9)_{k-1}\text{ holds at every root of type }k-1\Big),$$
--
--   and the energies (2.18) of the two systems agree:
--   $$E_{\mathfrak{gl}(M|N)}\big(\{u^{(l)}_j\}_{l=1}^{r}\big) = E_{\mathfrak{gl}(M-1|N-1)}\big(\{u^{(l)}_j\}_{l\ne k,k+1}\big).$$
--
--   The forward direction is the restriction R1–R2 of §4.1; the backward direction is the reduction of the lift in §4.2 to "finding a solution to either eq. (4.2) or eq. (4.4)". Together with the equality of energies this makes explicit the embedding of the $\mathfrak{gl}(M-1|N-1)$ Bethe spectrum into the $\mathfrak{gl}(M|N)$ one, which the paper uses to relate the $\mathfrak{gl}(n+N|N)$ chains with fixed $n$.
--
--   **Formalization Note.** The reduced system is the same Bethe predicate applied to the deleted grading on $d-2$ positions and the reindexed roots, with its own source terms and its own loop weight; nothing is passed to it by hand. Regularity (nonzero $\Lambda_k(u)$, $\Lambda_{k+1}(u)$ and nonzero denominators of (2.9) at every root of type $k$) is added as the non-degeneracy that the division form of (2.9) presupposes; it is imposed only on the original system. The standing assumption $n=M-N>0$ of p. 7 is kept as $N<M$; the algebra of §4 does not use it. The energy is the complex-valued expression (2.18) with $x^{(k)}_j$ as in (2.11), each computed in its own grading.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, pp. 17–19 (PDF 18–20), §4.1 A1, A2, R1–R2, eqs. (4.2)–(4.6), §4.2; energy (2.18), p. 6 (PDF 7); standing assumption p. 7 (PDF 8)

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace SuperBAE.Restriction

theorem bae_restriction (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hR1 : roots (k - 1) = roots (k + 1)) (hreg : Regular L odd d roots) :
    (IsBAESolution L odd d roots ↔
        (IsBAESolution L (delGrading k odd) (d - 2) (delRoots k roots) ∧
          ∀ u ∈ roots (k - 1), bae L odd d roots (k - 1) u)) ∧
      energy odd d roots = energy (delGrading k odd) (d - 2) (delRoots k roots) := by sorry

end SuperBAE.Restriction
