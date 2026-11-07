-- Prove2me | Theorems.Thm_SublinearSteiner_theorem_3_1
-- name    : SublinearSteiner.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:45:52.050958+00:00
-- url     : https://prove2.me/theorems/fbff69ca-265c-4d0f-ae42-a5f5f469c983
-- title:
--   Theorem 3.1 — structural theorem, (3.2), (3.3)
-- statement:
--   Let $a_*>0$, $u\in[0,1)$ and $a_i=a_*\omega^{i+u}$ for $i\in\mathbb Z$. Then
--   $$L\le\Bigl(2-\frac{89e_0}{90}\Bigr)\mathrm{OPT}+\frac{1001}{4000}\Gamma+e_0\Lambda.$$
--   In particular,
--   $$\Gamma\le e_0L/100\ \text{ and }\ \Lambda\le L/10\implies L\le(2-e_0/2)\,\mathrm{OPT}.$$
--   Both statements remain true if the sums in $\Gamma,\Lambda$ are restricted to the indices with $d_{\min}/2<a_i<2\Delta_T$, where $d_{\min}$ and $\Delta_T$ are the smallest and the largest distance between two distinct terminals.
--
--   The theorem says that if the terminal MST is not much more than twice $\mathrm{OPT}$ it is because of structure visible in two local statistics; it reduces estimation below factor 2 to measuring them.
--
--   Differences from the source:
--   - reading: sums over Z, and sums restricted to dmin/2 < a_i < 2Δ_T → sums over any finite J containing every index in the restricted range; reason: J equal to that range gives the restricted sums; a large J gives the unrestricted ones, whose summands vanish outside a finite set; it also covers k ≤ 1
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Theorem 3.1, (3.1), (3.2), (3.3), p.15

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Theorem 3.1 (Structural theorem), (3.2), (3.3), p.15. For every `a∗ > 0` and `u ∈ [0, 1)`,
`L ≤ (2 − 89e0/90) OPT + (1001/4000) Γ + e0 Λ`, and `Γ ≤ e0 L/100`, `Λ ≤ L/10` imply `L ≤ (2 − e0/2) OPT`. Both remain true if
the sums in (3.1) are restricted to the indices with `dmin/2 < a_i < 2Δ_T`.

**Formalization Note.** The statement holds for every finite `J ⊆ ℤ` containing every index with `dmin/2 < a_i < 2Δ_T`.
Taking `J` equal to that finite set gives the restricted sums. The unrestricted sums over `ℤ` have only finitely many nonzero
summands, so a large `J` gives them too. "`dmin/2 < a_i`" says that some pair of distinct terminals has `w < 2a_i`, and
"`a_i < 2Δ_T`" that some pair has `a_i < 2w`; this form also covers `|T| ≤ 1`, where no index is required. -/
theorem theorem_3_1 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (OPT L : ℝ)
    (hOPT : IsSteinerOpt T w OPT) (hL : IsTerminalMST T w L) (aStar u : ℝ) (haStar : 0 < aStar)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (J : Finset ℤ)
    (hJ : ∀ i : ℤ, (∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ w.d x y < 2 * idealScale aStar u i) →
      (∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ idealScale aStar u i < 2 * w.d x y) → i ∈ J) :
    L ≤ (2 - 89 * e0 / 90) * OPT + 1001 / 4000 * Gamma w T (idealScale aStar u) J
        + e0 * Lambda w T (idealScale aStar u) J ∧
      (Gamma w T (idealScale aStar u) J ≤ e0 * L / 100 → Lambda w T (idealScale aStar u) J ≤ L / 10 →
        L ≤ (2 - e0 / 2) * OPT) := by sorry

end SublinearSteiner
