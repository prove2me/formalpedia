-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_theorem_3_11
-- name    : QAdvFew.PoQOracle.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:59.032079+00:00
-- url     : https://prove2.me/theorems/520b0ef0-7cdf-4c33-8c42-8f345c5fab6e
-- title:
--   Theorem 3.11 — majority lower bound for $\mathsf{AC}^0[\oplus]$
-- statement:
--   Let $\mathrm{MAJ}$ be the majority function. For any $C\in\mathsf{AC}^0[\oplus](S,O(1))$,
--   $$\Pr_{x\leftarrow\{0,1\}^N}[C(x)=\mathrm{MAJ}(x)]\le\frac12+\frac{\mathrm{polylog}(S)}{\sqrt N}.$$
--
--   This average-case lower bound goes back to Razborov [Raz87]; the precise statement is Theorem 3 of [Hoz26]. Combined with a direct-product theorem it gives the hardness of salted majority.
--
--   Differences from the source:
--   - reading: polylog(S), O(1) → for every depth d a constant c with c(log₂S+1)^c, uniform in N, S and C; reason: the uniform reading of asymptotic notation: constants come after the fixed parameters and before the quantified objects
--   - encoding: N → N ≥ 1; reason: 1/√N is undefined at N = 0, and Lean's value 0 would make the bound false for a constant circuit
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 3.11, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_IsAC0Xor
import Definitions.Def_NoPerfectRandComp_maj

namespace QAdvFew.PoQOracle

/-- **Theorem 3.11 (Majority lower bound)** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, Theorem 3.11, p. 14 (PDF p. 16); [Raz87], Theorem 3
of [Hoz26]). For any `C ∈ AC0[⊕](S, O(1))`,
`Pr_{x←{0,1}^N}[C(x) = MAJ(x)] ≤ 1/2 + polylog(S)/√N`.

**Formalization Note** Uniform reading: for every depth `d` there is `c` with the bound
`1/2 + c (log₂ S + 1)^c / √N` for all `N ≥ 1`, `S` and circuits of `AC0[⊕](S, d)` on `N` inputs.
`N = 0`, where `1/√N` is undefined, is excluded. `MAJ` is the published
`NoPerfectRandComp.maj` (`MAJ(x) = 1` iff more than half the bits are `1`, as on p. 14). -/
theorem theorem_3_11 (d : ℕ) : ∃ c : ℝ, ∀ N S : ℕ, 1 ≤ N → ∀ C : Circuit (Fin N),
    IsAC0Xor C S d →
    ((Finset.univ.filter (fun x : Fin N → Bool =>
        C.eval1 (fun _ => false) x = NoPerfectRandComp.maj N x)).card : ℝ) /
        2 ^ N ≤ 1 / 2 + c * (Real.logb 2 S + 1) ^ c / Real.sqrt N := by sorry

end QAdvFew.PoQOracle
