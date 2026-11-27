-- Prove2me | Theorems.Thm_PalomarZF207_internal_provC1_implies_reg_halts
-- name    : PalomarZF207.internal_provC1_implies_reg_halts
-- status  : Open
-- author  : @fl-39
-- created : 2026-11-27T03:20:05.94081+00:00
-- url     : https://prove2.me/theorems/3655a075-1c01-5e1f-8506-29c74d77229f
-- title:
--   Internal completeness of the register machine for calculus $\mathsf{C}$
-- statement:
--   Let $(V, E)$ be a nonempty model of $\mathrm{ZF}$ satisfying the register-machine loop semantics `InternalLoopStep E`. If $(V, E)$ contains an internal finite refutation of falsity $1$ in the calculus $\mathsf{C}$ (`InternalProvC1 E`), then starting from the initial register-machine frame at prefix $1$ with registers $(0, 0, 0, 0, 0, 0, 2, 0, 0)$ and positive gap/tail parameters $m, t > 0$, the 207-state Turing machine reaches a terminal configuration in internally finitely many steps:
--
--   $$
--   \mathrm{InternalLoopStep}_E \;\wedge\; \mathrm{InternalProvC1}_E \;\longrightarrow\; \mathrm{InternalHaltsFrom}_E(\mathrm{frame}_0).
--   $$
--
--   The proof compiles an arbitrary (possibly nonstandard) internal $\mathsf{C}$-derivation of $1$ into a command word $W \ge 2$ that forces halting from any retained stack/register store, and uses internal induction on the scheduler counter $r_6$ to show the machine halts before or upon executing $W$.
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Sections 2 and 6 (Lemma 6.1, command-word completeness)

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_internal_prov
import Definitions.Def_palomar_zf207_internal_tm

namespace PalomarZF207
theorem internal_provC1_implies_reg_halts :
    ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
      PalomarZF207InternalTM.InternalLoopStep E →
      PalomarZF207Internal.InternalProvC1 E →
      ∀ (m t z two c1 : V),
        PalomarZF207History.Empty E z →
        PalomarZF207History.Numeral E 2 two →
        ¬ PalomarZF207History.Empty E m →
        ¬ PalomarZF207History.Empty E t →
        PalomarZF207InternalTM.FrameCodeV E 1 m ⟨z, z, z, z, z, z, two, z, z⟩ t c1 →
        PalomarZF207InternalTM.InternalHaltsFrom E c1 := by sorry
end PalomarZF207
