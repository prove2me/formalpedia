-- Prove2me | Theorems.Thm_RandOrderCSP_theorem_7_1
-- name    : RandOrderCSP.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:50.673958+00:00
-- url     : https://prove2.me/theorems/f07b78c3-351b-4aa7-a4c1-0d90758242f6
-- title:
--   Theorem 7.1 — weighted block-singleton-free level inequality
-- statement:
--   Let $U$ be a finite set, $\mathcal P$ a partition of $U$, and $q,s,t,\ell\in\mathbb N$ with $q\ge2$. If $f\in\mathcal F_U(s)$, $1\le t\le s$ and $1\le\ell\le t/2$, then
--
--   $$\sum_{Z\in\mathbb Z_q^U,\ \mathrm{supp}(Z)\in\mathrm{SF}_{\mathcal P}(t,\ell)}q^{-\mathrm{vol}(\mathcal P(Z))}\,|\hat f(Z)|^2\le\Big(\frac{2qs}{t-\ell}\Big)^{t-\ell}.$$
--
--   This hypercontractive estimate supplies the Fourier decay used to keep posteriors bounded.
--
--   Differences from the source:
--   - encoding: q ∈ ℕ → 2 ≤ q; reason: the paper fixes q ≥ 2 for Z_q on p.10
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Theorem 7.1, p.29

import Mathlib
import Definitions.Def_RandOrderCSP_blockVol
import Definitions.Def_RandOrderCSP_fourierCoeff

namespace RandOrderCSP

/-- **Theorem 7.1 (weighted block-singleton-free level inequality).** Singer, Tulsiani, Velusamy, *A
dichotomy theorem for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript
sha256 3aca9d2f…), Theorem 7.1, p.29.

**Formalization Note.** `q ≥ 2` is the paper's convention (p.10). `1 ≤ ℓ ≤ t/2` is `2ℓ ≤ t`, so the
natural-number difference `t - ℓ` is the true one. The negative power of `q` is real-valued. -/
theorem theorem_7_1 {U : Type} [Fintype U] [DecidableEq U]
    (P : Finpartition (Finset.univ : Finset U)) (q s t ℓ : ℕ) [NeZero q] (hq : 2 ≤ q)
    (f : (U → ZMod q) → ℂ) (hf : InFamilyF (s : ℝ) f) (ht : 1 ≤ t) (hts : t ≤ s) (hℓ : 1 ≤ ℓ)
    (hℓt : 2 * ℓ ≤ t) :
    (∑ Z ∈ Finset.univ.filter (fun Z : U → ZMod q => IsSFtl P t ℓ (vsupp Z)),
        (q : ℝ) ^ (-(blockVol P (vsupp Z) : ℝ)) * ‖fourierCoeff f Z‖ ^ 2) ≤
      (2 * (q : ℝ) * s / ((t - ℓ : ℕ) : ℝ)) ^ (t - ℓ) := by sorry

end RandOrderCSP
