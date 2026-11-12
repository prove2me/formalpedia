-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_lemma_9
-- name    : SubcubicBA.PlainPKI.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:53.796753+00:00
-- url     : https://prove2.me/theorems/5677e88d-bd89-47e9-beac-2a34889a0151
-- title:
--   Lemma 9 — ComputeProof finds a proof whenever one exists
-- statement:
--   Let $V$ be a set of votes $(p,v)$ with $p<n$ and $v\in\{0,1,\bot\}$, let $A$ be a set of accusations between parties $<n$, and let $b\in\{0,1\}$. Let $Q$ be the set of parties with a vote for $b$ or $\bot$ in $V$, let $E$ be the set of accusations of $A$ disjoint from $Q$, and let $M$ be **any** maximum matching of $E$. If some $V_0\subseteq V$ and $A_0\subseteq A$ form a proof for $b$ (Definition 10), then
--   1. $|Q|\ge1$ and $|Q|+|M|\ge t+1$, so ComputeProof$(b)$ succeeds; and
--   2. every selection it may return is a proof for $b$: if $V'\subseteq V$ consists of votes for $b$ or $\bot$ with distinct voters, $M'\subseteq M$, $|V'|\ge1$ and $|V'|+|M'|=t+1$, then $(V',M')$ is a proof for $b$.
--
--   ComputeProof is complete for the proofs available from the received votes and accusations.
--
--   Differences from the source:
--   - reading: Q, the votes in Votes for v or ⊥ → the parties having a vote for b or ⊥ (one vote per party is selected); reason: v is a typo for b; Definition 10 needs distinct voters, so Q counts parties
--   - encoding: a maximum matching computed by the algorithm; a returned set of t + 1 votes/accusations → every maximum matching M and every admissible selection (V′, M′); reason: the source's arbitrary choices, quantified universally
--   - encoding: votes and accusations held by an honest party → party indices < n and vote values ≤ 2 as hypotheses; reason: they are the validated items ProofCreation passes to ComputeProof
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Lemma 9, p. 19 (ComputeProof, p. 19)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs

namespace SubcubicBA.PlainPKI

/-- Lemma 9 (p. 19). -/
theorem lemma_9 (n t b : ℕ) (hb : b ≤ 1) (V A : Finset (ℕ × ℕ))
    (hV : ∀ x ∈ V, x.1 < n ∧ x.2 ≤ 2) (hA : ∀ y ∈ A, y.1 < n ∧ y.2 < n)
    (hex : ∃ V₀ ⊆ V, ∃ A₀ ⊆ A, IsProofSet n t b V₀ A₀)
    (M : Finset (ℕ × ℕ)) (hM : IsMaxAccMatching (proofE b V A) M) :
    (1 ≤ (proofQ b V).card ∧ t + 1 ≤ (proofQ b V).card + M.card) ∧
    ∀ V' M' : Finset (ℕ × ℕ), V' ⊆ V.filter (fun x => x.2 = b ∨ x.2 = 2) →
      (∀ x ∈ V', ∀ x' ∈ V', x.1 = x'.1 → x = x') → M' ⊆ M → 1 ≤ V'.card →
      V'.card + M'.card = t + 1 → IsProofSet n t b V' M' := by sorry

end SubcubicBA.PlainPKI
