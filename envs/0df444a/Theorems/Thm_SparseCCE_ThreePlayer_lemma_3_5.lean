-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_5
-- name    : SparseCCE.ThreePlayer.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:07:49.899272+00:00
-- url     : https://prove2.me/theorems/8f364365-a647-49da-80b0-d3fbf18a25b1
-- title:
--   Lemma 3.5 — the reference laws $\hat\nu_i$ are causal, rational, polynomial-time computable, and $\nu_{ik}\le18T\,\hat\nu_i\otimes\hat\nu_k$
-- statement:
--   Let $\Gamma$ be a repeated game and $\mu$ a $T$-sparse law of action profiles of a normal-form game whose actions contain transcripts. Suppose $\mathrm{err}_i(\nu_{ik})\le\delta\le M^{-3}$ for all players $i\ne k$, and let $k_i$ be a partner choice (every pair of players is $\{i,k_i\}$). Then for all reference laws $\hat\nu_i=\frac13(\bar\nu_i^c+\nu_i^c+\mathrm{unif}_i)$ of $\mu$: every $\hat\nu_i$ is causal; $\nu_{ik}(z,\tilde z)\le18T\,\hat\nu_i(z)\hat\nu_k(\tilde z)$ for all $i\ne k$; and each $\hat\nu_j$ represents every decoding $x_j$ of it.
--
--   Moreover, for each of the mixture and probability-table input formats there is a polynomial-time algorithm that, given $M$ in unary, the sizes of $\Gamma$, the partners, the transcripts of the normal-form actions and $\mu$ by rational weights and components (`refInput`) or by its rational probability table (`refTableInput`), outputs, for every player, a listing of rational laws $\hat\nu_i$ that are reference laws of $\mu$.
--
--   Differences from the source:
--   - encoding: a repeated game Γ described in words (§3.2: nature and the players move in a fixed order, each player once, signals determined by earlier moves of the round) → RepeatedGame over a RoundProtocol with nonempty move sets, a fixed move order and availability, and nature kernels indexed by round and public history, satisfying WellFormed; reason: This retains the sequential protocol without imposing stationary independent nature moves; rounds are indexed 0, …, H−1
--   - generalization: the laws given by Lemma 3.2 and the repaired laws, with the conditional answer laws arbitrary at probability-zero pairs → the causality, domination and representation claims hold for every admissible choice (IsReferenceLaws); reason: covers every choice, so it specializes to the source’s construction
--   - reading: the laws ν̂_i are rational and computable from µ in time polynomial in M and in the encoding length of µ → there is a polynomial-time algorithm whose output lists rational laws that are reference laws of µ for some admissible choice; reason: arbitrary choices at probability-zero pairs need not be rational; the computed laws are the ones the source’s algorithm produces
--   - encoding: the encoding of µ and of the game → refInput: M in unary, |players|, H, |O|, |Θ_j|, |A_j|, the partners, the transcript code of every action (via enumerations), and µ by rational weights and components; output: per player a listing of (transcript code, rational probability); reason: time polynomial in M and the length of µ becomes polynomial time in the input length; the construction uses only the transcript structure, so any enumeration serves
--   - encoding: fix another player k_i so that every pair of players has the form {i, k_i} → IsPartnerChoice k, for any finite set of players; reason: the source’s condition verbatim
--   - encoding: "by Lemma 3.4(a), each ν̂_j represents x_j" → a third conclusion: every decoding x_j of ν̂_j is represented by ν̂_j; reason: the statement asserts it
--   - generalization: the positive-horizon repeated games used in the paper → the identities also cover H = 0 and a finite player set that may be empty; reason: At H = 0 there is one empty play and transcript, λ = 1 and every causality error is zero; with no players the well-formed nature protocol is still a probability law. All source instances are retained
--   - encoding: µ may be given by weights and components or by its probability table (pp. 13, 19) → separate uniform polynomial-time algorithms for refInput and refTableInput; the table clause assumes IsTSparse over real components; reason: Both source representations are retained, without assuming that a rational table has a rational factorization
--   - generalization: the private signal determined by earlier moves of a round → the signal rule may additionally depend on the round and public history, while still ignoring later moves; reason: The history is already observed; the simulation identities use only that the signal is determined before the player acts. Taking the round protocol’s signal rule gives the source setting
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.5, p. 17; proof App. A.3, pp. 30–31.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts
import Definitions.Def_SparseCCE_ThreePlayer_ReferenceProfile

namespace SparseCCE.ThreePlayer

open RepeatedGame

/-- **Lemma 3.5 (Reference profile)**, p. 17: let `μ` be `T`-sparse with
`err_i(ν_{ik}) ≤ δ ≤ M^{-3}` for all players `i ≠ k`; with partners `k_i` and the laws
`ν̂_i = (ν̄_i^c + ν_i^c + unif_i)/3` built from `μ`, the laws `ν̂_i` are causal, rational, computable
from `μ` in time polynomial in `M` and in the encoding length of `μ`, and satisfy
`ν_{ik} ≤ 18T ν̂_i ⊗ ν̂_k` for all players `i ≠ k`; each `ν̂_j` represents its decoding `x_j`. -/
theorem lemma_3_5 :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι), Γ.WellFormed →
      ∀ {B : ι → Type} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
        (tr : (j : ι) → B j → Γ.Transcript j) (T : ℕ) (μ : ((j : ι) → B j) → ℝ),
        IsTSparse T μ → ∀ (k : ι → ι), IsPartnerChoice k → ∀ δ : ℝ,
        (∀ i l, i ≠ l → Γ.err (Γ.recPairLaw tr μ i l) ≤ δ) → δ ≤ ((Γ.Mmax : ℝ) ^ 3)⁻¹ →
        ∀ νhat : (j : ι) → Γ.Transcript j → ℝ, Γ.IsReferenceLaws tr μ k νhat →
          (∀ i, Γ.IsCausal (νhat i)) ∧
          (∀ i l, i ≠ l → ∀ z z', Γ.recPairLaw tr μ i l z z' ≤ 18 * (T : ℝ) * νhat i z * νhat l z') ∧
          ∀ x : Γ.StrategyProfile, (∀ j, Γ.IsDecoding (νhat j) (x j)) →
            ∀ j, Γ.Represents (νhat j) (x j)) ∧
    (∃ alg : List Bool → List Bool, CookPvsNP.PolyTimeComputable alg ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι), Γ.WellFormed →
      ∀ (E : Γ.Enumeration) {B : ι → Type} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
        (tr : (j : ι) → B j → Γ.Transcript j) (eB : (j : ι) → B j ≃ Fin (Fintype.card (B j)))
        (T : ℕ) (w : Fin T → ℚ) (p : Fin T → (j : ι) → B j → ℚ),
        IsDist (fun t => (w t : ℝ)) → (∀ t j, IsDist (fun b => (p t j b : ℝ))) →
        ∀ (k : ι → ι), IsPartnerChoice k → ∀ δ : ℝ,
        (∀ i l, i ≠ l → Γ.err (Γ.recPairLaw tr
          (mixture (fun t => (w t : ℝ)) (fun t j b => (p t j b : ℝ))) i l) ≤ δ) →
        δ ≤ ((Γ.Mmax : ℝ) ^ 3)⁻¹ →
        ∃ νq : (j : ι) → Γ.Transcript j → ℚ,
          Γ.IsReferenceLaws tr (mixture (fun t => (w t : ℝ)) (fun t j b => (p t j b : ℝ))) k
            (fun j z => (νq j z : ℝ)) ∧
          ∃ outs : ι → List Bool, (∀ j, IsLawListing E.trCode (νq j) (outs j)) ∧
            alg (refInput E tr eB k w p) =
              (List.finRange (Fintype.card ι)).flatMap (fun jj => outs (E.eι.symm jj))) ∧
    ∃ alg : List Bool → List Bool, CookPvsNP.PolyTimeComputable alg ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι), Γ.WellFormed →
      ∀ (E : Γ.Enumeration) {B : ι → Type} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
        (tr : (j : ι) → B j → Γ.Transcript j) (eB : (j : ι) → B j ≃ Fin (Fintype.card (B j)))
        (T : ℕ) (μ : ((j : ι) → B j) → ℚ), IsTSparse T (fun b => (μ b : ℝ)) →
        ∀ (k : ι → ι), IsPartnerChoice k → ∀ δ : ℝ,
        (∀ i l, i ≠ l → Γ.err (Γ.recPairLaw tr (fun b => (μ b : ℝ)) i l) ≤ δ) →
        δ ≤ ((Γ.Mmax : ℝ) ^ 3)⁻¹ →
        ∃ νq : (j : ι) → Γ.Transcript j → ℚ,
          Γ.IsReferenceLaws tr (fun b => (μ b : ℝ)) k (fun j z => (νq j z : ℝ)) ∧
          ∃ outs : ι → List Bool, (∀ j, IsLawListing E.trCode (νq j) (outs j)) ∧
            alg (refTableInput E tr eB k T μ) =
              (List.finRange (Fintype.card ι)).flatMap (fun jj => outs (E.eι.symm jj)) := by sorry

end SparseCCE.ThreePlayer
