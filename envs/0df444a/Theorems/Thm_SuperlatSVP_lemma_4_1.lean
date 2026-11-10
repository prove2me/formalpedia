-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_4_1
-- name    : SuperlatSVP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:29.952708+00:00
-- url     : https://prove2.me/theorems/1e391991-fc15-4271-bc53-420083fd7227
-- title:
--   Lemma 4.1 — for large $n$, $\rho_{\sqrt{2n/(3\pi e)}/\lambda}(L^*)\le p/q$, and $p\ge q$
-- statement:
--   Assume the standing setting of §4.1:
--
--   - $L=B\mathbb Z^n$ with $\det L=1$;
--   - the point-count bound $N_L(r\lambda_1(L))\le b^nr^n$ ($r\ge1$) with $b=2^\beta\ge\sqrt{4/3}$;
--   - $\lambda_1(L)\le\lambda\le(1+n^{-2})\lambda_1(L)$;
--   - a prime $p$ in the range (4.7), $q(3b^2/4)^{n/2}/\operatorname{vol}(A)\le p\le2q(3b^2/4)^{n/2}/\operatorname{vol}(A)$, where $q=2^{\lceil n/\log_2n\rceil}$ and $A$ is the midpoint shell.
--
--   Then for all sufficiently large $n$,
--   $$\rho_{\sqrt{2n/(3\pi e)}/\lambda}(L^*)\le\frac pq,\qquad\text{and in particular }p\ge q .$$
--
--   Together with Lemma 3.1 this shows that $\Gamma_0$ is smooth at width $\lambda\sqrt{3\pi e/(2n)}$.
--
--   **Formalization Note** "Sufficiently large $n$" is one threshold $n_0$, chosen before the lattice, $\lambda$, $\beta$ and $p$.
--
--   Differences from the source:
--   - encoding: for sufficiently large n → ∃ n₀ ∀ n ≥ n₀, with n₀ chosen before the lattice, λ, β and p; reason: the source's asymptotic constants are uniform over the related parameters (p.14)
--   - encoding: Gaussian masses as real sums → sums of nonnegative terms in [0,∞]; reason: Lean convention; the sums are finite for lattices, so no instance changes
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.1, p.32 (PDF p.32), Lemma 4.1

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_shellA
import Definitions.Def_SuperlatSVP_Sec41Setting
import Definitions.Def_RegevLWE_GaussConv_Lattice

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 4.1 (Bounding dual Gaussian mass of L∗). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.1, p.32 (PDF p.32): "For sufficiently
large n, ρ_{√(2n/(3πe))/λ}(L∗) ≤ p/q. In particular, p ≥ q."

The setting is the §4.1 standing assumptions (`Sec41Setting`: det L = 1, (2.3) with
`b = 2^β ≥ √(4/3)`, `λ₁(L) ≤ λ ≤ (1+n^{−2})λ₁(L)`, a prime `p` in the range (4.7)).

**Formalization Note.** "Sufficiently large n" is one threshold `n₀`, chosen before the lattice,
`λ`, `β` and `p`. Mass in `ℝ≥0∞`; `L*` is `RegevLWE.GaussConv.dual`. -/
theorem lemma_4_1 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℝ) (lam β : ℝ) (p : ℕ),
      p.Prime → Sec41Setting n B lam β p →
        rhoSet (Real.sqrt (2 * n / (3 * Real.pi * Real.exp 1)) / lam)
            (RegevLWE.GaussConv.dual (lat B) : Set (E n)) ≤ (p : ℝ≥0∞) / (chainQ n : ℝ≥0∞) ∧
          chainQ n ≤ p := by sorry

end SuperlatSVP
