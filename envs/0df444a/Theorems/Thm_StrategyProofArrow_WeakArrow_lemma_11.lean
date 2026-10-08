-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakArrow_lemma_11
-- name    : StrategyProofArrow.WeakArrow.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:19.582572+00:00
-- url     : https://prove2.me/theorems/ece51678-d21a-4b23-8589-2939f65aa9cc
-- title:
--   Lemma 11 — breaking the social ordering's ties by a regular tie-breaker preserves CS, NNR and IIA
-- statement:
--   Let $n\ge 2$ and $m\ge 3$, let $u$ be a social welfare function on weak ballot sets, and let $Q$ be a strong order on $S_m$. Define a new social welfare function by breaking the ties of each social ordering according to $Q$:
--
--   $$\mu(B)=\gamma\big[u(B)\big],\qquad x\ \mu(B)\ y \iff x\,\overline{u(B)}\,y\ \text{ or }\ \big(x,y \text{ tied in } u(B) \text{ and } x\,Q\,y\big).$$
--
--   If $u$ satisfies CS, NNR and IIA, then $\mu$ has range contained in $\rho_m$ and satisfies CS, NNR and IIA.
--
--   This lemma lets the proof of Theorem 3' pass from an arbitrary Arrovian social welfare function to one with strong-order range, to which Lemma 10 applies.
--
--   **Formalization Note** The paper applies a regular tie-breaking function $\gamma$, defined on ballot sets, to the single ordering $u(B)$; we read this as the component tie-breaker with tie-breaking order $Q$, the order the proof of Theorem 3' calls "$Q\in\rho_m$, the tie-breaking order for $\gamma$". The printed "define the social welfare function $u^{nm}$" is read as $\mu^{nm}$, as (44) shows. The range claim holds by construction (the tie-broken order is a strong order) and is stated as the first conjunct. CS is stated for distinct alternatives.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 11, (44), p. 48

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Lemma 11**, Satterthwaite p. 48: let `u` be a social welfare function on weak ballot sets,
with `n ≥ 2` and `m ≥ 3`, and let `μ(B) = γ[u(B)]` break the ties of each social ordering by a
regular tie-breaker with tie-breaking order `Q`. If `u` satisfies CS, NNR and IIA, then `μ` has
range contained in the strong orders and satisfies CS, NNR and IIA. -/
theorem lemma_11 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (Q : StrongOrder A)
    (hCS : CS u) (hNNR : NNR u) (hIIA : IIA u) :
    (∀ B, (breakTies Q (u B)).1.IsStrong) ∧
      CS (fun B => (breakTies Q (u B)).1) ∧
      NNR (fun B => (breakTies Q (u B)).1) ∧
      IIA (fun B => (breakTies Q (u B)).1) := by sorry

end StrategyProofArrow.WeakArrow
