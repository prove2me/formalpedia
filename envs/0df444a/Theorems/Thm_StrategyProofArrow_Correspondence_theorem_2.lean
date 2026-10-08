-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_theorem_2
-- name    : StrategyProofArrow.Correspondence.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:22.082663+00:00
-- url     : https://prove2.me/theorems/1021a8cd-bc96-4cb3-b0cf-bed6d7f4dbde
-- title:
--   Theorem 2 — strict strategy-proof voting procedures with full range correspond one-to-one to strict SWFs with CS, NNR, IIA
-- statement:
--   Let $I_n$ be a committee of $n\ge2$ individuals and $S_m$ a set of $m\ge3$ alternatives. There is a one-to-one correspondence $\lambda$ between
--
--   - the strict voting procedures $v:\rho_m^n\to S_m$ that are strategy-proof and have range $T_p=S_m$, and
--   - the strict social welfare functions $u:\rho_m^n\to\rho_m$ that satisfy citizens' sovereignty, non-negative response and independence of irrelevant alternatives,
--
--   such that, whenever $u=\lambda(v)$, $u$ underlies $v$ and $v$ is derived from $u$:
--   $$\Psi_{S_m}[\lambda(v)(B)]=\{v(B)\}\qquad\text{for every } B\in\rho_m^n.$$
--
--   The theorem says that, for strict preferences, strategy-proofness of a voting procedure is equivalent to Arrow's conditions on the social welfare function underlying it, independently of the fact that each set of conditions forces dictatorship.
--
--   **Formalization Note** $\lambda$ is a Lean `Equiv` between the two subtypes, together with the condition that $\lambda(v)$ underlies $v$ for every $v$; "underlies" and "derived from" are the same relation (`Underlies`). A bare bijection would be a cardinality statement and lose the content. Procedures and social welfare functions are functions on strict ballot sets only (a subtype), so two of them are equal iff they agree on every admissible ballot set. CS is read for $x\ne y$, NNR for every $x$; the range is taken over strict ballot sets.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Theorem 2, p. 35

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem theorem_2 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
:
    ∃ lam : {v : StrongProfile ι A → A // StrategyProof v ∧ Set.range v = Set.univ} ≃
        {u : StrongProfile ι A → StrongOrder A // CS u ∧ NNR u ∧ IIA u},
      ∀ v, Underlies (lam v).1 v.1 := by sorry

end StrategyProofArrow.Correspondence
