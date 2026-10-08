-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_theorem_6_3
-- name    : TwinWidthI.MinorFree.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:39.173826+00:00
-- url     : https://prove2.me/theorems/796a7286-060c-432c-a82d-339ff29030d4
-- title:
--   Theorem 6.3 — every K_t-minor-free graph has twin-width at most 4c_{g(t)}·2^(4c_{g(t)}+2)
-- statement:
--   For every nonnegative integer $t$, a finite graph $G$ with no $K_t$ minor has twin-width at most $f(t)$, with the explicit proof-supported constants
--
--   $$
--   g(t)=2(2^{4t+1}+2)^2,\qquad
--   c_k=\frac83(k+1)^2 2^{4k},\qquad
--   f(t)=4c_{g(t)}2^{4c_{g(t)}+2}.
--   $$
--
--   Thus the class of graphs excluding a fixed clique minor has bounded twin-width, with a bound depending only on $t$ and independent of the graph's order.
--
--   **Formalization Note** Twin-width is natural-number valued, so the Lean conclusion uses $\lfloor f(t)\rfloor$. The theorem statement on p. 3:26 prints $g(t)=2(2^{4t+1}+1)^2$, but its proof sets $h(t)=2^{4t+1}+2$ and $g(t)=2h(t)^2$; the latter is formalized. For $t=0$ the minor-free hypothesis is impossible, and for $t=1$ it forces an empty graph.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:26–3:29, Theorem 6.3 and proof, with proof's g(t)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_TwinWidthI_MinorFree_Setting

namespace TwinWidthI.MinorFree

/-- Theorem 6.3, using the proof's `g(t)=2(2^(4t+1)+2)^2` rather than the printed `+1`.
The bound is the explicit one on p. 3:29. -/
theorem theorem_6_3 (t : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : SimpleGraph (Fin t)) G) :
    TwinWidthI.BoolWidth.TwinWidthLE G ⌊fMF t⌋₊ := by sorry

end TwinWidthI.MinorFree
