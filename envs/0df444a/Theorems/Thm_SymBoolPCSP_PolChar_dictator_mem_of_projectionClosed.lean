-- Prove2me | Theorems.Thm_SymBoolPCSP_PolChar_dictator_mem_of_projectionClosed
-- name    : SymBoolPCSP.PolChar.dictator_mem_of_projectionClosed
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-05T19:24:27.91564+00:00
-- url     : https://prove2.me/theorems/02118172-3ed7-4722-a056-def8ba0811bc
-- title:
--   A projection-closed family containing $\mathrm{id}_D$ contains every dictator
-- statement:
--   Let $\mathcal F$ be a family of functions over a domain $D$ (for each arity $L$, a set of functions $D^L \to D$). Suppose $\mathcal F$ is projection-closed, i.e. $f \in \mathcal F$ of arity $L \ge 1$ implies $f^{\pi} \in \mathcal F$ for every $\pi : [L] \to [R]$ with $R \ge 1$, and suppose $\mathrm{id}_D \in \mathcal F$. Then for every arity $R$ and every $j \in [R]$ the dictator
--
--   $$
--   y \mapsto y_j, \qquad D^R \to D,
--   $$
--
--   belongs to $\mathcal F$.
--
--   This is the step in the proof of Lemma 6.7 of Brakensiek–Guruswami that gives $P \subseteq Q$ for the canonical promise relation; more generally it says that projection-closed families containing the identity contain all projections, as polymorphism families always do.
--
--   **Formalization Note** The arity $R$ is positive automatically because $j : \mathrm{Fin}\,R$ exists. `ProjectionClosed` and `ContainsId` are the platform definitions from `SymBoolPCSP_PolChar_Basic`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §6.2, proof of Lemma 6.7, pp. 29–30

import Mathlib
import Definitions.Def_SymBoolPCSP_PolChar_Basic

namespace SymBoolPCSP.PolChar

/-- A projection-closed family of functions containing the unary identity contains every
dictator `y ↦ y_j` of every arity `R`. -/
theorem dictator_mem_of_projectionClosed {D : Type} (F : FunFamily D)
    (hpc : ProjectionClosed F) (hid : ContainsId F) {R : ℕ} (j : Fin R) :
    (fun y : Fin R → D => y j) ∈ F R := by sorry

end SymBoolPCSP.PolChar
