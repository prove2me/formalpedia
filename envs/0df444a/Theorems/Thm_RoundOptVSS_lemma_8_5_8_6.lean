-- Prove2me | Theorems.Thm_RoundOptVSS_lemma_8_5_8_6
-- name    : RoundOptVSS.lemma_8_5_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:05:53.674471+00:00
-- url     : https://prove2.me/theorems/551503bb-3fb5-4d1d-beee-b1472c34fc79
-- title:
--   Lemmas 8.5 and 8.6 — correctness and commitment of the compiler on $G$
-- statement:
--   **Lemma 8.5** (Correctness). On $G$, if the dealer is honest, every honest party outputs $x$.
--
--   **Lemma 8.6** (Commitment). On $G$, there is a value $s^*\in\mathbb E^h\cup\{\bot\}$ determined by the honest parties' views at the end of sharing such that every honest party outputs $s^*$.
--
--   Stated, as Lemma 8.4, for Protocol 9's output $D_{0,i}(k^\star)$ under the facts used on $G$: those of Lemma 8.4 for the mask instances, and for the root instance with committed value $\rho_0$: (a) for every honest-consistent $k$ all honest parties obtain $\bot$ or all obtain $\rho_0$, and if the dealer is honest with input $x$ all obtain $x$; (b) the rejection is the same for all honest-consistent root openings. The conclusion: with $Z_0$ the least fixed point of Lemma 8.4, there is $s^*\in\{\bot,\rho_0\}$ with
--
--   $$s^*=\bot\iff D_{0,i_0}(k^\star;\tau_0')=\bot$$
--
--   for every honest $i_0$ and every honest-consistent root openings $\tau_0'$; every honest party outputs $s^*$ whatever the corrupt mask announcements; and $s^*=x$ if the dealer is honest.
--
--   Differences from the source:
--   - generalization: on G, for the concrete compiler → for any decoders, searches and openings satisfying the facts of Lemma 8.4 and (a), (b), correctness for the root; reason: these are the facts the proofs use on G
--   - reading: s∗ "determined by the honest parties' views at the end of sharing" → s∗ ∈ {⊥, ρ₀}, ⊥ iff the root rejects k⋆ at any honest party under any honest-consistent root openings; reason: ρ₀ and k⋆ are fixed by the sharing phase; the rejection is independent of the party and of corrupt openings
--   - encoding: two lemmas → one item, both conclusions; reason: they share the setting
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Lemmas 8.5 and 8.6 with proofs (p.30), Protocol 9 (p.28)

import Mathlib
import Definitions.Def_RoundOptVSS_Recovery

namespace RoundOptVSS

/-- **Lemma 8.5** (Correctness) and **Lemma 8.6** (Commitment), p.30 of Liu-Zhang, Masserova,
*Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity*, manuscript
(STOC 2027 submission, sha256 3a45d95d…): on `G`, if the dealer is honest, every honest party
outputs `x`; and on `G` there is a value `s⋆ ∈ 𝔼^h ∪ {⊥}` determined by the honest parties' views
at the end of sharing such that every honest party outputs `s⋆`.

Stated for Protocol 9's output `D_{0,i}(k⋆)` given the facts the proof uses on `G`: the data and
facts of Lemma 8.4 for the mask instances (exact searches, (a), correctness of honest owners,
(b)), and for the root instance `O₀` with decoders `D_{0,i}(·; τ₀)`, committed value `ρ₀` and
actual openings `τ₀`: (a) for every honest-consistent `k` all honest parties obtain `⊥` or all
obtain `ρ₀`, and if the dealer is honest with input `x` they all obtain `x`; (b) the rejection
`D_{0,i}(k; τ₀′) = ⊥` is the same for all honest-consistent `τ₀′`.

Conclusion: with `Z₀` the least fixed point of Lemma 8.4 (for every honest party and every
honest-consistent openings), there is `s⋆ ∈ {⊥, ρ₀}` such that `s⋆ = ⊥` iff `D_{0,i₀}(k⋆; τ₀′) = ⊥`
for every honest `i₀` and every honest-consistent `τ₀′` (`k⋆` bad on `Z₀`, canonical elsewhere),
every honest party outputs `s⋆` whatever the corrupt announced masks, and `s⋆ = x` if the dealer
is honest.

**Formalization Note.** As in Lemma 8.4, decoders, searches and openings are abstract data
satisfying the facts that hold on `G`; `s⋆` is a function of `Z₀`, `c`, `ρ₀` and the rejection
decision, which is independent of the party and of the corrupt openings. -/
theorem lemma_8_5_8_6 {𝔼 : Type} [Field 𝔼] {n m h : ℕ} {Op : Type}
    (C : Finset (Fin n)) (dealer : Fin n) (lam : 𝔼) (Cdep : Fin n → Option (Fin m → 𝔼))
    (ρ : Fin n → Fin m → 𝔼)
    (Dm : Fin n → Fin n → (Fin n → Op) → KeyAssign 𝔼 n m → Option (Fin m → 𝔼))
    (Srch : Fin n → Fin n → (Fin n → Op) → Finset (Fin n) → KeyAssign 𝔼 n m → SearchMode →
      Option (KeyAssign 𝔼 n m))
    (τ : Fin n → Fin n → Op)
    (D0 : Fin n → (Fin n → Op) → KeyAssign 𝔼 n m → Option (Fin h → 𝔼)) (τ0 : Fin n → Op)
    (ρ0 x : Fin h → 𝔼)
    (hS : ∀ i a τa Z c b,
      (∀ k, Srch i a τa Z c b = some k →
        k ∈ KSet Cdep Z c ∧ (Dm i a τa k = none ↔ b = SearchMode.rej)) ∧
      (Srch i a τa Z c b = none →
        ∀ k ∈ KSet Cdep Z c, ¬ (Dm i a τa k = none ↔ b = SearchMode.rej)))
    (ha : ∀ a (k : KeyAssign 𝔼 n m), (∀ j, j ∉ C → k j = keyOf lam (Cdep j) (some (ρ j))) →
      (∀ i, i ∉ C → Dm i a (τ a) k = none) ∨ (∀ i, i ∉ C → Dm i a (τ a) k = some (ρ a)))
    (hcorr : ∀ a, a ∉ C → ∀ k : KeyAssign 𝔼 n m,
      (∀ j, j ∉ C → k j = keyOf lam (Cdep j) (some (ρ j))) →
        ∀ i, i ∉ C → Dm i a (τ a) k = some (ρ a))
    (hb : ∀ a i, i ∉ C → ∀ k : KeyAssign 𝔼 n m,
      (∀ j, j ∉ C → k j = keyOf lam (Cdep j) (some (ρ j))) →
      ∀ τ₁ τ₂ : Fin n → Op, (∀ j, j ∉ C → τ₁ j = τ a j) → (∀ j, j ∉ C → τ₂ j = τ a j) →
        (Dm i a τ₁ k = none ↔ Dm i a τ₂ k = none))
    (ha0 : ∀ k : KeyAssign 𝔼 n m, (∀ j, j ∉ C → k j = keyOf lam (Cdep j) (some (ρ j))) →
      (∀ i, i ∉ C → D0 i τ0 k = none) ∨ (∀ i, i ∉ C → D0 i τ0 k = some ρ0))
    (hcorr0 : dealer ∉ C → ∀ k : KeyAssign 𝔼 n m,
      (∀ j, j ∉ C → k j = keyOf lam (Cdep j) (some (ρ j))) → ∀ i, i ∉ C → D0 i τ0 k = some x)
    (hb0 : ∀ i, i ∉ C → ∀ k : KeyAssign 𝔼 n m,
      (∀ j, j ∉ C → k j = keyOf lam (Cdep j) (some (ρ j))) →
      ∀ τ₁ τ₂ : Fin n → Op, (∀ j, j ∉ C → τ₁ j = τ0 j) → (∀ j, j ∉ C → τ₂ j = τ0 j) →
        (D0 i τ₁ k = none ↔ D0 i τ₂ k = none)) :
    let c : KeyAssign 𝔼 n m := fun j => keyOf lam (Cdep j) (some (ρ j))
    ∃ Z0 : Finset (Fin n), Z0 ⊆ C ∧
      (∀ i0, i0 ∉ C → ∀ τ' : Fin n → Fin n → Op, (∀ a j, j ∉ C → τ' a j = τ a j) →
        IsLeastFixedPoint (Phi Cdep c (fun a => Dm i0 a (τ' a))) Z0) ∧
      ∃ sStar : Option (Fin h → 𝔼), (sStar = none ∨ sStar = some ρ0) ∧
        (∀ i0, i0 ∉ C → ∀ τ0' : Fin n → Op, (∀ j, j ∉ C → τ0' j = τ0 j) →
          (sStar = none ↔ D0 i0 τ0' (starOf Z0 c) = none)) ∧
        (∀ i, i ∉ C → ∀ Rhat : Fin n → Option (Fin m → 𝔼), (∀ j, j ∉ C → Rhat j = some (ρ j)) →
          D0 i τ0 (protocol9Assign lam Cdep (fun a => Dm i a (τ a)) (fun a => Srch i a (τ a)) Rhat) =
            sStar) ∧
        (dealer ∉ C → sStar = some x) := by sorry

end RoundOptVSS
