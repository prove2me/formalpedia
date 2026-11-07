-- Prove2me | Theorems.Thm_TwoBoxMemory_proposition_B_6
-- name    : TwoBoxMemory.proposition_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:45.275961+00:00
-- url     : https://prove2.me/theorems/dae9595f-d1bb-49c6-bfc2-9ee0cda71f54
-- title:
--   Proposition B.6 — finite-budget robustness under a cost change
-- statement:
--   Fix failure probabilities $r,s\in(0,1)$, a cost $D>0$ for command $B$ and a cost $C^*>0$ for command $A$. Write $V^*$, $\Delta^*_M$ for the value and the excess at $(C^*,D)$, and $\Delta'_M$ for the excess at $(C',D)$. If $0\le\eta<1$ and $(1-\eta)C^*\le C'\le(1+\eta)C^*$, then for every integer $M\ge1$
--
--   $$(1-\eta)\Delta^*_M-2\eta V^*\ \le\ \Delta'_M\ \le\ (1+\eta)\Delta^*_M+2\eta V^* .$$
--
--   It transfers finite-budget gap inequalities from a series-defined saddle cost to a nearby rational cost.
--
--   Differences from the source:
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: V* ∈ [0, ∞] → V*.toReal; reason: V* is finite for r, s ∈ (0, 1), C*, D > 0 (verification file)
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Proposition B.6, (B.20), p.27 (PDF 29); (8.2), p.11 (PDF 13)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- Proposition B.6 (Finite-budget robustness under a cost change). Fix `r, s ∈ (0, 1)`, `D > 0`
and a cost `C* > 0`, and write `V*`, `Δ*_M` for `(C*, D)` and `Δ′_M` for `(C′, D)`. If `0 ≤ η < 1`
and `(1 − η) C* ≤ C′ ≤ (1 + η) C*`, then for every integer `M ≥ 1`,
`(1 − η) Δ*_M − 2η V* ≤ Δ′_M ≤ (1 + η) Δ*_M + 2η V*` (B.20).

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Proposition B.6, (B.20), p.27 (PDF 29); (8.2), p.11 (PDF 13).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem proposition_B_6 (r s D Cs C' η : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s)
    (hs1 : s < 1) (hD : 0 < D) (hCs : 0 < Cs) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hlo : (1 - η) * Cs ≤ C') (hhi : C' ≤ (1 + η) * Cs) (M : ℕ) (hM : 1 ≤ M) :
    (1 - η) * gap r s Cs D M - 2 * η * (value r s Cs D).toReal ≤ gap r s C' D M ∧
    gap r s C' D M ≤ (1 + η) * gap r s Cs D M + 2 * η * (value r s Cs D).toReal := by sorry

end TwoBoxMemory
