-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_lemma_7
-- name    : StrategyProofArrow.Correspondence.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:45.830618+00:00
-- url     : https://prove2.me/theorems/07c11314-3a04-452b-823f-49641d35eef3
-- title:
--   Lemma 7 — the voting procedure derived from a strict SWF with CS, NNR, IIA is strategy-proof with full range
-- statement:
--   Consider a strict committee with $n\ge2$ individuals and $m\ge3$ alternatives, and a strict social welfare function $u:\rho_m^n\to\rho_m$ satisfying CS, NNR and IIA. Then:
--
--   1. a voting procedure $v:\rho_m^n\to S_m$ derived from $u$ exists, that is, one with $\Psi_{S_m}[u(B)]=\{v(B)\}$ for every $B\in\rho_m^n$;
--   2. every voting procedure $v$ derived from $u$ is strategy-proof and has range
--   $$T_p=\{v(B): B\in\rho_m^n\}=S_m.$$
--
--   Lemma 7 is the first half of the correspondence of Theorem 2: it maps every Arrovian strict social welfare function to a strict strategy-proof voting procedure with full range.
--
--   **Formalization Note** "The voting procedure derived from $u$" is formalized relationally through `Underlies u v`, together with the existence of such a $v$; for a strong social ordering on a finite set the top element is unique, so this is the paper's derived procedure. The range is taken over strict ballot sets. CS is read for $x\ne y$, NNR for every $x$.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 7, p. 30

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem lemma_7 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hcs : CS u) (hnnr : NNR u) (hiia : IIA u) :
    (∃ v : StrongProfile ι A → A, Underlies u v) ∧
      ∀ v : StrongProfile ι A → A, Underlies u v →
        StrategyProof v ∧ Set.range v = Set.univ := by sorry

end StrategyProofArrow.Correspondence
