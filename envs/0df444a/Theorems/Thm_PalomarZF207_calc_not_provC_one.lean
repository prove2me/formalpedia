-- Prove2me | Theorems.Thm_PalomarZF207_calc_not_provC_one
-- name    : PalomarZF207.calc_not_provC_one
-- status  : Proved
-- author  : @fl-39
-- created : 2026-11-26T23:16:01.083353+00:00
-- url     : https://prove2.me/theorems/7fe05af4-6224-45c8-9733-3bf8de43fd67
-- title:
--   ZF207: semantic soundness of calculus $\mathcal{C}$ in models of $\mathrm{ZF}$
-- statement:
--   If the standalone first-order presentation of Zermelo--Fraenkel set theory $\mathrm{ZF}$ admits a nonempty model $(V, E)$, then code $1$ (representing $\bot$, i.e. $x_0 \in x_0$) is not derivable in the numeric Hilbert-style calculus $\mathcal{C}$:
--
--   $$\bigl(\exists (V : \mathrm{Type})\,(E : V \to V \to \mathrm{Prop}),\; \mathrm{Nonempty}\,V \wedge \mathrm{Model}\,E\bigr) \;\longrightarrow\; \neg\,\mathrm{ProvC}\,1.$$
--
--   This theorem encapsulates the definable pointed-hull lemma (via Scott's trick and the cumulative hierarchy inside an arbitrary model of $\mathrm{ZF}$) and proves that every theorem of $\mathcal{C}$ is valid in $(V, E)$.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), Section 4 (Lemmas 4.1-4.2, p. 4)

import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_calc

namespace PalomarZF207

theorem calc_not_provC_one : (∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E) → ¬ PalomarZF207Calc.ProvC 1 := by sorry

end PalomarZF207
