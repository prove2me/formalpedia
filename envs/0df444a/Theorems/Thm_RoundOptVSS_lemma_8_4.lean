-- Prove2me | Theorems.Thm_RoundOptVSS_lemma_8_4
-- name    : RoundOptVSS.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:06:05.991802+00:00
-- url     : https://prove2.me/theorems/c0c409f6-e9cf-4cb5-829f-f09cffb631e6
-- title:
--   Lemma 8.4 — recovery: every honest party obtains the same honest-consistent, sharing-fixed assignment $k^\star$
-- statement:
--   **Lemma 8.4** (Recovery). On the good event $G$, every honest party obtains the same assignment $k^\star$, which is honest-consistent and determined by the honest parties' views at the end of sharing.
--
--   Stated for Protocol 9's local computation under the facts its proof uses on $G$. Let $C$ be the corrupt set, $C_j$ the deposits, $\rho_a$ the committed masks and $c_j=\mathrm{Key}(C_j,\rho_j)$ the canonical vector; $k$ is honest-consistent if $k_j=c_j$ for every honest $j$. Assume
--
--   1. every search $\mathrm{Search}_a$ is exact over $\mathcal K(Z,c)$ on every input;
--   2. (a) for every honest-consistent $k$, all honest parties obtain $\bot$ from instance $a$ or all obtain $\rho_a$, and all obtain $\rho_a$ if the owner $a$ is honest;
--   3. (b) for every honest-consistent $k$ the rejection $D_{a,i}(k;\tau)=\bot$ is the same for all honest-consistent opening vectors $\tau$.
--
--   Then there is $Z_0\subseteq C$ which is the least fixed point of $\Phi(Z)=Z\cup\{a:\exists k\in\mathcal K(Z,c),\ D_{a,i_0}(k;\tau')=\bot\}$ for every honest $i_0$ and every honest-consistent openings $\tau'$, such that every honest party, whatever the corrupt parties announce as masks, obtains
--
--   $$k^\star_j=\begin{cases}\mathrm{bad},&j\in Z_0,\\ c_j,&j\notin Z_0,\end{cases}$$
--
--   and $k^\star$ is honest-consistent.
--
--   Differences from the source:
--   - generalization: on G, for the concrete compiler with the WSS of §7 → for any decoders, searches and openings satisfying search exactness, (a), correctness of honest owners and (b); reason: these are the facts the proof uses on G (p.29); they hold on G by Lemma 8.3 and Definition 7.7
--   - reading: "determined by the honest parties' views at the end of sharing" → k⋆ = bad on Z₀, c elsewhere, with Z₀ the least fixed point of Φ for every honest party and all honest-consistent openings, the same for all corrupt mask announcements; reason: c is fixed by the sharing phase and Φ does not depend on the party or on reconstruction-time data
--   - encoding: Protocol 9's unbounded "restart" loops → loops with fuel n + 1; reason: at most n + 1 passes and n + 1 scans (p.28)
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Lemma 8.4 and its proof (pp.29–30), Protocol 9 (p.28)

import Mathlib
import Definitions.Def_RoundOptVSS_Recovery

namespace RoundOptVSS

/-- **Lemma 8.4** (Recovery), pp.29–30 of Liu-Zhang, Masserova, *Round-Optimal Statistical
Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027 submission, sha256
3a45d95d…): on `G`, every honest party obtains the same assignment `k⋆`, which is
honest-consistent and determined by the honest parties' views at the end of sharing.

Stated for the local computation of Protocol 9 given the facts the proof uses on `G`. Data: the
corrupt set `C`, `λ`, the deposits `C_j`, the committed masks `ρ_a`, the canonical vector
`c_j = Key(C_j, ρ_j)`, the decoders `D_{a,i}(·; τ_a)` of the mask instances at each party `i`
under opening vectors `τ_a`, the lifted searches `Search_a` at each party, and the actual
openings `τ`. Facts (honest-consistent: `k_j = c_j` for every honest `j`):
* `Search_a` is exact on every input over `𝒦(Z, c)` (Definition 7.7 and the lift of §8.2);
* (a) uniform weak commitment: for every honest-consistent `k`, all honest parties obtain `⊥` or
  all obtain `ρ_a`; for an honest owner `a`, all obtain `ρ_a`;
* (b) sharing-determined rejection: `D_{a,i}(k; τ₁) = ⊥ ⇔ D_{a,i}(k; τ₂) = ⊥` for all
  honest-consistent `k, τ₁, τ₂`.

Conclusion: there is `Z₀ ⊆ C`, the least fixed point of `Φ(Z) = Z ∪ {a : ∃ k ∈ 𝒦(Z, c),
D_{a,i₀}(k; τ′_a) = ⊥}` for every honest `i₀` and every honest-consistent opening vectors `τ′`
(so `Z₀` does not depend on the party or on the corrupt openings), such that for every honest `i`
and every vector of announced masks `R̂` with `R̂_j = ρ_j` for honest `j` (the corrupt
announcements are arbitrary), Protocol 9 at `i` returns `k⋆` = bad on `Z₀` and `c` elsewhere;
`k⋆` is honest-consistent.

**Formalization Note.** The decoders, searches and openings are abstract: any data satisfying
the listed facts, which hold on `G` (Lemma 8.3) for the concrete scheme. -/
theorem lemma_8_4 {𝔼 : Type} [Field 𝔼] {n m : ℕ} {Op : Type}
    (C : Finset (Fin n)) (lam : 𝔼) (Cdep : Fin n → Option (Fin m → 𝔼))
    (ρ : Fin n → Fin m → 𝔼)
    (Dm : Fin n → Fin n → (Fin n → Op) → KeyAssign 𝔼 n m → Option (Fin m → 𝔼))
    (Srch : Fin n → Fin n → (Fin n → Op) → Finset (Fin n) → KeyAssign 𝔼 n m → SearchMode →
      Option (KeyAssign 𝔼 n m))
    (τ : Fin n → Fin n → Op)
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
        (Dm i a τ₁ k = none ↔ Dm i a τ₂ k = none)) :
    let c : KeyAssign 𝔼 n m := fun j => keyOf lam (Cdep j) (some (ρ j))
    ∃ Z0 : Finset (Fin n), Z0 ⊆ C ∧
      (∀ i0, i0 ∉ C → ∀ τ' : Fin n → Fin n → Op, (∀ a j, j ∉ C → τ' a j = τ a j) →
        IsLeastFixedPoint (Phi Cdep c (fun a => Dm i0 a (τ' a))) Z0) ∧
      (∀ j, j ∉ C → starOf Z0 c j = c j) ∧
      ∀ i, i ∉ C → ∀ Rhat : Fin n → Option (Fin m → 𝔼), (∀ j, j ∉ C → Rhat j = some (ρ j)) →
        protocol9Assign lam Cdep (fun a => Dm i a (τ a)) (fun a => Srch i a (τ a)) Rhat =
          starOf Z0 c := by sorry

end RoundOptVSS
