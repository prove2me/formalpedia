-- Prove2me | Theorems.Thm_RoundOptVSS_lemma_A_5
-- name    : RoundOptVSS.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:05:51.66516+00:00
-- url     : https://prove2.me/theorems/84fb4481-735d-43e0-b6db-d9da5eddfa90
-- title:
--   Lemma A.5 — exact attainable EARLY outcomes: $x_L$ iff $h_0+z\ge t+1$, $\bot$ iff $h_0\le t$, with explicit keys $K^\pm$
-- statement:
--   **Lemma A.5** (Exact attainable outcomes). Consider an EARLY label in the remaining case of §A.4: it is active and unreplaced, its candidate polynomial $P_L$ is valid with $\deg P_L\le\delta_L$ and payload $x_L=\mathrm{val}(P_L)$, and its checkpoint $(d_L,T_L)$ is well formed. Let $Z\subseteq[n]$ be the free parties, $c_w$ the fixed key slots of $w\notin Z$, $z=|Z|$ and
--
--   $$h_0=\sum_{w\notin Z}\mathrm{Check}_L(c_w[L]),\qquad \mathcal O_L(Z)=\{\mathrm{Early}(L;k):k\in\mathcal K(Z,c)\}.$$
--
--   Then
--
--   $$x_L\in\mathcal O_L(Z)\iff h_0+z\ge t+1,\qquad \bot\in\mathcal O_L(Z)\iff h_0\le t.$$
--
--   Every attainable outcome has an explicitly constructible assignment of the free key slots: for any $\alpha\in\mathcal A_L$, giving $K^+=(\alpha,P_L(\alpha),0)$ to the free parties of a set $S\subseteq Z$ and $K^-=(\alpha,P_L(\alpha)+1,T_L(\alpha)-d_L(P_L(\alpha)+1))$ to the other free parties realizes $x_L$ whenever $h_0+|S|\ge t+1$, and $S=\emptyset$ realizes $\bot$ whenever $h_0\le t$.
--
--   This lemma is what makes the key search of the compiler polynomial: a free key is a free vote.
--
--   Differences from the source:
--   - encoding: the slot of label L in assignments k ∈ 𝒦(Z, c) of full verification vectors → one label's slots Fin n → Option (𝔼 × 𝔼 × 𝔼), free on Z and equal to c outside Z; reason: the outcome of L depends only on its own slots
--   - reading: "Every attainable outcome has an explicitly constructible assignment of the free key slots of L" → the assignments K⁺ on S, K⁻ on Z \ S (any α ∈ 𝒜) realize x_L when h₀ + |S| ≥ t + 1 and ⊥ (S = ∅) when h₀ ≤ t; reason: the witnesses of the proof
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Lemma A.5 and its proof (p.38), with the setting of §A.4 (pp.37–38)

import Mathlib
import Definitions.Def_RoundOptVSS_PackedIC

open scoped Polynomial
open Polynomial Classical

namespace RoundOptVSS

/-- **Lemma A.5** (Exact attainable outcomes), p.38 of Liu-Zhang, Masserova, *Round-Optimal
Statistical Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027
submission, sha256 3a45d95d…). In the remaining case of §A.4 (an active, unreplaced EARLY label
with a valid candidate polynomial `P_L`, `deg P_L ≤ δ_L`, payload `x_L = val(P_L)`, and a
well-formed checkpoint `(d_L, T_L)`, `d_L ∈ 𝔽^×`, `deg T_L ≤ δ_L`), with free set `Z`, fixed key
slots `c_w` outside `Z`, `z = |Z|` and `h₀ = Σ_{w ∉ Z} Check_L(c_w[L])`, and
`O_L(Z) = {Early(L; k) : k ∈ 𝒦(Z, c)}`:

`x_L ∈ O_L(Z) ⇔ h₀ + z ≥ t + 1` and `⊥ ∈ O_L(Z) ⇔ h₀ ≤ t`.

Every attainable outcome has an explicitly constructible assignment of the free key slots: for
any `α ∈ A_L`, give `K⁺ = (α, P(α), 0)` to the free parties in `S` and
`K⁻ = (α, P(α) + 1, T(α) − d(P(α) + 1))` to the other free parties; this realizes `x_L` whenever
`h₀ + |S| ≥ t + 1`, and with `S = ∅` realizes `⊥` whenever `h₀ ≤ t`.

**Formalization Note.** One label's key slots are `Fin n → Option (𝔼 × 𝔼 × 𝔼)` (`none` = bad);
`Early` in this case is `earlyOpen` (value `x_L` iff at least `t + 1` of all `n` votes accept,
else ⊥ = `none`). -/
theorem lemma_A_5 {𝔽 𝔼 : Type} [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (I : ICParams 𝔽) (hI : I.Standing) {n : ℕ} (P : 𝔼[X]) (hP : P.natDegree ≤ I.δ)
    (cp : 𝔽 × 𝔼[X]) (hcp : CpValid I cp) (Z : Finset (Fin n))
    (c : Fin n → Option (ICKey 𝔼)) :
    let h0 := (Finset.univ.filter fun w => w ∉ Z ∧ Check I (val I P) P cp (c w)).card
    let K : Set (Fin n → Option (ICKey 𝔼)) := {k | ∀ w, w ∉ Z → k w = c w}
    let wit : 𝔽 → Finset (Fin n) → Fin n → Option (ICKey 𝔼) := fun α S w =>
      if w ∈ Z then (if w ∈ S then some (keyPlus α P) else some (keyMinus α P cp)) else c w
    ((∃ k ∈ K, earlyOpen I (val I P) P cp k = some (val I P)) ↔ I.t + 1 ≤ h0 + Z.card) ∧
    ((∃ k ∈ K, earlyOpen I (val I P) P cp k = none) ↔ h0 ≤ I.t) ∧
    (∀ α ∈ I.A, ∀ S ⊆ Z, I.t + 1 ≤ h0 + S.card →
      wit α S ∈ K ∧ earlyOpen I (val I P) P cp (wit α S) = some (val I P)) ∧
    (∀ α ∈ I.A, h0 ≤ I.t → wit α ∅ ∈ K ∧ earlyOpen I (val I P) P cp (wit α ∅) = none) := by sorry

end RoundOptVSS
