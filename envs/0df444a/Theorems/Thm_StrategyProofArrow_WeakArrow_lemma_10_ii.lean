-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakArrow_lemma_10_ii
-- name    : StrategyProofArrow.WeakArrow.lemma_10_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:37.776136+00:00
-- url     : https://prove2.me/theorems/bb162e50-81f9-46ad-bc04-d4e8e60004e6
-- title:
--   Lemma 10 (second sentence) — an Arrovian SWF with strong-order range factors as a strict Arrovian SWF after a tie-breaking function
-- statement:
--   Let $n\ge 2$ and $m\ge 3$, and let $u$ be a social welfare function on weak ballot sets $B\in\pi_m^n$ whose range is contained in the strong orders $\rho_m$. If $u$ satisfies IIA, CS and NNR, then there exist a tie-breaking function $\alpha$ and a strict social welfare function $\mu$ satisfying IIA, CS and NNR such that
--
--   $$u(B)=\mu\big(\alpha(B)\big)\qquad\text{for all } B\in\pi_m^n .$$
--
--   The tie-breaking function $\alpha$ need not be regular: its value on individual $i$ may depend on the whole ballot set. This decomposition reduces Arrow's theorem with indifference to the strict case.
--
--   **Formalization Note** The standing hypothesis of Lemma 10, range contained in $\rho_m$, applies to this sentence and is kept. CS is stated for distinct alternatives. Conventions are those of the definitions file.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 10, second sentence, p. 44

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Lemma 10, second sentence**, Satterthwaite p. 44: let `u` be a social welfare function on weak
ballot sets with range contained in the strong orders. If `u` satisfies IIA, CS and NNR, then there
exist a tie-breaking function `α` and a strict social welfare function `μ` satisfying IIA, CS and
NNR such that `u(B) = μ(α(B))` for every weak ballot set `B`. -/
theorem lemma_10_ii {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (hrange : ∀ B, (u B).IsStrong)
    (hIIA : IIA u) (hCS : CS u) (hNNR : NNR u) :
    ∃ α : WeakProfile ι A → StrongProfile ι A, IsTieBreaking α ∧
      ∃ μ : StrongProfile ι A → StrongOrder A,
        StrictIIA μ ∧ StrictCS μ ∧ StrictNNR μ ∧ ∀ B, u B = (μ (α B)).1 := by sorry

end StrategyProofArrow.WeakArrow
