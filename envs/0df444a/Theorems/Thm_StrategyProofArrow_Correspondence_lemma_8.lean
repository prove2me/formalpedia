-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_lemma_8
-- name    : StrategyProofArrow.Correspondence.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:29.427987+00:00
-- url     : https://prove2.me/theorems/f80d85bb-0b32-4689-ac76-5fade1d6cc5d
-- title:
--   Lemma 8 — a strict strategy-proof procedure with full range has a unique underlying strict SWF with CS, NNR, IIA
-- statement:
--   Consider a strict committee with $n\ge2$ individuals and $m\ge3$ alternatives, and a strict voting procedure $v:\rho_m^n\to S_m$ with range $T_p=S_m$. If $v$ is strategy-proof, then there exists a unique strict social welfare function $u:\rho_m^n\to\rho_m$ such that
--   $$\Psi_{S_m}[u(B)]=\{v(B)\}\ \text{ for all } B\in\rho_m^n,\qquad u\text{ satisfies CS, NNR and IIA}.$$
--
--   Lemma 8 is the second half of the correspondence of Theorem 2.
--
--   **Formalization Note** Uniqueness is equality of functions on strict ballot sets (a subtype), so junk values on non-admissible profiles cannot break it. The range is taken over strict ballot sets. CS is read for $x\ne y$, NNR for every $x$.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 8, p. 35

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem lemma_8 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v) (hrange : Set.range v = Set.univ) :
    ∃! u : StrongProfile ι A → StrongOrder A, Underlies u v ∧ CS u ∧ NNR u ∧ IIA u := by sorry

end StrategyProofArrow.Correspondence
