-- Prove2me | Theorems.Thm_PalomarZF207_godel2_from_hbl
-- name    : PalomarZF207.godel2_from_hbl
-- status  : Proved
-- author  : @fl-39
-- created : 2026-11-27T00:02:35.31246+00:00
-- url     : https://prove2.me/theorems/c6173408-c370-45f2-afc1-34a3f8351d0b
-- title:
--   Gödel's Second Incompleteness Theorem from Hilbert–Bernays–Löb conditions
-- statement:
--   Let $\Box : \mathrm{Formula} \to \mathrm{Formula}$ preserve closedness and satisfy the Hilbert–Bernays–Löb derivability conditions (D1)–(D3) on closed formulas of `PalomarZF207`, together with a Gödel fixed point $G$ satisfying $\mathrm{ZF} \vdash G \leftrightarrow \neg\Box G$. If ZF is consistent, then $\mathrm{ZF} \nvdash \neg\Box\bot$.
-- source:
--   Kurt Gödel (1931) / Hilbert–Bernays–Löb derivability conditions, applied inside PalomarZF207 natural deduction (cf. James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Lemma 1.3)

import Definitions.Def_palomar_zf207_zf

namespace PalomarZF207
theorem godel2_from_hbl (Box : Formula → Formula) (hClosed : ∀ φ, Closed φ → Closed (Box φ)) (hD1 : ∀ φ, Closed φ → Provable φ → Provable (Box φ)) (hD2 : ∀ φ ψ, Closed φ → Closed ψ → Provable (.imp (Box (.imp φ ψ)) (.imp (Box φ) (Box ψ)))) (hD3 : ∀ φ, Closed φ → Provable (.imp (Box φ) (Box (Box φ)))) (hDiag : ∃ G, Closed G ∧ Provable (sourceIff G (Neg (Box G)))) : Consistent → ¬ Provable (Neg (Box .bot)) := by sorry
end PalomarZF207
