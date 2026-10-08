-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakArrow_lemma_10_i
-- name    : StrategyProofArrow.WeakArrow.lemma_10_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:28.587244+00:00
-- url     : https://prove2.me/theorems/2e5f0225-b2de-4833-8cdc-f135dff4a9b7
-- title:
--   Lemma 10 (first sentence) — a regular tie-breaking composition of a strict Arrovian SWF satisfies IIA, CS and NNR
-- statement:
--   Let $n\ge 2$ and $m\ge 3$, and let $u$ be a social welfare function on weak ballot sets $B\in\pi_m^n$ whose range is contained in the strong orders $\rho_m$. Suppose that for every $B\in\pi_m^n$
--
--   $$u(B)=\mu\big(\gamma(B)\big),$$
--
--   where $\gamma$ is a regular tie-breaking function and $\mu$ is a strict social welfare function satisfying IIA, CS and NNR. Then $u$ satisfies IIA, CS and NNR.
--
--   The two sentences of Lemma 10 describe tie-breaking compositions in both directions. Regularity is required for the forward preservation claim; the factorization in the second sentence permits any tie-breaking function.
--
--   **Formalization Note** The paper prints the hypothesis as "$u^{nm}(B)=u^{nm}[\gamma(B)]$", a misprint for $u^{nm}(B)=\mu^{nm}[\gamma(B)]$: the sentence names $\mu$ and the proof (p. 44) writes "Let $u^{nm}(B)=\mu^{nm}[\gamma(B)]$". The paper's committee is printed $\langle I_m,S_m,u^{nm}\rangle$, read $\langle I_n,S_m,u^{nm}\rangle$. The range hypothesis on $u$ is kept as printed. CS is stated for distinct alternatives. Conventions are those of the definitions file.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 10, first sentence, p. 44

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Lemma 10, first sentence**, Satterthwaite p. 44: let `u` be a social welfare function on weak
ballot sets with range contained in the strong orders. If `u(B) = μ(γ(B))` for every `B`, where
`γ` is a regular tie-breaking function and `μ` is a strict social welfare function satisfying IIA,
CS and NNR, then `u` satisfies IIA, CS and NNR. (The printed `u^{nm}(B) = u^{nm}[γ(B)]` is read as
`μ^{nm}[γ(B)]`, as the proof writes it.) -/
theorem lemma_10_i {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (hrange : ∀ B, (u B).IsStrong)
    (γ : WeakProfile ι A → StrongProfile ι A) (hγ : IsRegular γ)
    (μ : StrongProfile ι A → StrongOrder A)
    (hIIA : StrictIIA μ) (hCS : StrictCS μ) (hNNR : StrictNNR μ)
    (hu : ∀ B, u B = (μ (γ B)).1) :
    IIA u ∧ CS u ∧ NNR u := by sorry

end StrategyProofArrow.WeakArrow
