-- Prove2me | Theorems.Thm_TwoBoxMemory_sectionB8_profiles
-- name    : TwoBoxMemory.sectionB8_profiles
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:45.123011+00:00
-- url     : https://prove2.me/theorems/a35dda9c-b96a-4c70-b303-eb45417c84a6
-- title:
--   §B.8 — the finite profiles at $M=28,29$ and the 29-cycle
-- statement:
--   Let $W$ be the greedy word of $r=1/7$, $s=2/3$, $\beta=5/4$. Then
--
--   $$(D_{28},H_{28},F_{28})=(27,46,56),\qquad (D_{29},H_{29},F_{29})=(359,388,389);$$
--
--   the pair $(13,19)$ attains $H_{28}$ ($19+\ell(13,19)=46$) and $(0,29)$ attains $H_{29}$ ($29+\ell(0,29)=388$). The 29-cycle $\mathtt{ABBBBBABBBBBABBBBABBBBBABBBBB}$ has five $A$'s and 24 $B$'s; its periodic word agrees with $W$ for exactly 388 commands, the deterministic cycle controller giving probability $1$ to the first 388 letters of $W$ and $0$ to the first 389; and those 388 commands contain 67 $A$'s and 321 $B$'s.
--
--   These finite data fix the budgets of the jump.
--
--   Differences from the source:
--   - encoding: the cycle matches 388 commands, after which its next command is wrong → W_k = cycle_{k mod 29} for k < 388, W_388 ≠ cycle_{388 mod 29}, and the cycle controller's cylinder probabilities of the 388- and 389-prefixes of W are 1 and 0; reason: same statement for the periodic word and its controller
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §B.8, p.26 (PDF 28); Appendix G, p.57 (PDF 59)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
import Definitions.Def_TwoBoxMemory_Instance
open MeasureTheory

namespace TwoBoxMemory

/-- §B.8, the finite profiles at `r = 1/7`, `s = 2/3`, `β = 5/4`. For the greedy word `W`:
`(D₂₈, H₂₈, F₂₈) = (27, 46, 56)` and `(D₂₉, H₂₉, F₂₉) = (359, 388, 389)`; the pairs `(13, 19)`
and `(0, 29)` attain `H₂₈` and `H₂₉`; the 29-cycle `ABBBBBABBBBBABBBBABBBBBABBBBB` has five `A`s and
24 `B`s; its periodic word agrees with `W` for exactly 388 commands (the cycle controller's
cylinder probability of the first 388 letters of `W` is `1`, of the first 389 is `0`); the matched
prefix contains 67 `A`s and 321 `B`s.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§B.8, p.26 (PDF 28); Appendix G, p.57 (PDF 59).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem sectionB8_profiles :
    profD (greedyWord (1 / 7) (2 / 3) (5 / 4)) 28 = 27 ∧ profH (greedyWord (1 / 7) (2 / 3) (5 / 4)) 28 = 46 ∧
    profF (greedyWord (1 / 7) (2 / 3) (5 / 4)) 28 = 56 ∧ profD (greedyWord (1 / 7) (2 / 3) (5 / 4)) 29 = 359 ∧
    profH (greedyWord (1 / 7) (2 / 3) (5 / 4)) 29 = 388 ∧ profF (greedyWord (1 / 7) (2 / 3) (5 / 4)) 29 = 389 ∧
    19 + commonPrefix (greedyWord (1 / 7) (2 / 3) (5 / 4)) 13 19 = 46 ∧
    29 + commonPrefix (greedyWord (1 / 7) (2 / 3) (5 / 4)) 0 29 = 388 ∧
    (Finset.univ.filter fun k => cycle29 k = 0).card = 5 ∧
    (Finset.univ.filter fun k => cycle29 k = 1).card = 24 ∧
    (∀ k : ℕ, k < 388 → (greedyWord (1 / 7) (2 / 3) (5 / 4)) k = cycle29 ⟨k % 29, Nat.mod_lt _ (by norm_num)⟩) ∧
    (greedyWord (1 / 7) (2 / 3) (5 / 4)) 388 ≠ cycle29 ⟨388 % 29, by norm_num⟩ ∧
    cylProb cycleController (wordPrefix (greedyWord (1 / 7) (2 / 3) (5 / 4)) 388) = 1 ∧
    cylProb cycleController (wordPrefix (greedyWord (1 / 7) (2 / 3) (5 / 4)) 389) = 0 ∧
    greedyCounts (1 / 7) (2 / 3) (5 / 4) 388 = (67, 321) := by sorry

end TwoBoxMemory
