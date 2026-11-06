-- Prove2me | Theorems.Thm_UninformedMG_lemma_B_5
-- name    : UninformedMG.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:11.370458+00:00
-- url     : https://prove2.me/theorems/9946275d-4107-4c41-846f-2e355ca0928f
-- title:
--   Lemma B.5 — general drift–cost bound: some $q\in\mathcal Q(z)$ has $\Phi_R(z,q)\le cS$
-- statement:
--   Let $0<\lambda\le1/(2S)$ and fix $z\in\mathcal Z$ with induced weights $w$ and policies $\pi$. Assume that every candidate $v$ of the (finite, nonempty) class satisfies $v_1=v_{H+1}=0$ and $0\le v_h(s)\le1$. For each $(h,s)$ let $R_h(s,p)$ be a nonnegative local cost on distributions $p\in\Delta(\mathcal V)$ supported on $\mathrm{supp}(w)$, and let $\Phi_R$ be as in (32). Write $m_G=\sum_{v\in G}w(v)$ and $p^G(v)=w(v)\mathbf 1\{v\in G\}/m_G$. Suppose that there is $c\ge2\lambda$ such that, for every nonempty $G\subseteq\mathrm{supp}(w)$,
--   $$R_h(s,p^G)\le\frac c{m_G}\qquad\text{for all }h\in[H],\ s\in S_h.$$
--   Then there is $q\in\mathcal Q(z)$ such that, for every initial state $s_1\in S_1$,
--   $$\Phi_R(z,q)\le cS.$$
--
--   In particular $\min_{q\in\mathcal Q(z)}\Phi_R(z,q)\le cS$ whenever the minimum exists. Lemma B.6 applies it with the bandit cost (22).
--
--   Differences from the source:
--   - reading: min_{q∈𝒬(z)} Φ_R(z,q) ≤ cS → there is q ∈ 𝒬(z) with Φ_R(z,q) ≤ cS; reason: for an arbitrary local cost R the minimum need not be attained; the ∃ form equals "min ≤ cS" wherever the minimum exists
--   - generalization: the bound for the given initial state s₁ → one q serving every initial state s₁; reason: the proof's q⋆ is built by backward induction without reference to s₁ (p.9: a common minimizer for all s₁); fixing s₁ gives the printed lemma
--   - encoding: R_h(s,·) defined on distributions supported on supp(w) → a total function whose nonnegativity is assumed on those distributions; reason: Φ_R(z,q) reads R only there for q ∈ 𝒬(z), since λq ≤ w
--   - encoding: z ∈ 𝒵 → the pair (w, π) of Eq. (4); reason: every z ∈ 𝒵 is w·π and every quantity used is unchanged by π at w(v) = 0
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Lemma B.5, p.22 (PDF p.24), proof pp.22–23

import Mathlib
import Definitions.Def_UninformedMG_Phi

namespace UninformedMG

/-- **Lemma B.5 (General drift–cost bound)** (p.22 = PDF p.24; proof to p.23). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

Let `0 < λ ≤ 1/(2S)`. Fix `z ∈ Z` with induced weights `w` and policies `π`. Assume every candidate
satisfies `v_1 = v_{H+1} = 0` and `0 ≤ v_h(s) ≤ 1`. For each `(h, s)` let `R_h(s, p)` be a nonnegative
local cost on distributions `p ∈ Δ(V)` supported on `supp(w)`, and `Φ_R` as in Eq. (32). With
`m_G = ∑_{v∈G} w(v)` and `p^G(v) = w(v)1{v ∈ G}/m_G`, suppose there is `c ≥ 2λ` such that
`R_h(s, p^G) ≤ c/m_G` for every nonempty `G ⊆ supp(w)` and all `h, s`. Then `min_{q∈Q(z)} Φ_R(z,q) ≤ cS`.

**Formalization Note.** Generic finite candidate class. The conclusion is read as: some
`q ∈ Q(z)` has `Φ_R(z, q) ≤ cS`, and one such `q` serves every initial state `s₁` (the proof's
`q⋆` does not depend on `s₁`). For an arbitrary `R` the minimum need not be attained. -/
theorem lemma_B_5 {H : ℕ} (hH : 2 ≤ H) (G : Game H) (V : CandClass G)
    (hV0 : ∀ v (s : G.St 0), V.val v 0 s = 0)
    (hVlast : ∀ v (s : G.St (Fin.last H)), V.val v (Fin.last H) s = 0)
    (hVnn : ∀ v h s, 0 ≤ V.val v h s) (hVle : ∀ v h s, V.val v h s ≤ 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (w : V.C → ℝ) (π : CPolicy V) (hz : IsJoint V w π)
    (Rc : (h : Fin H) → G.St h.castSucc → (V.C → ℝ) → ℝ)
    (hRnn : ∀ h s p, p ∈ stdSimplex ℝ V.C → (∀ v, w v = 0 → p v = 0) → 0 ≤ Rc h s p)
    (c : ℝ) (hc : 2 * lam ≤ c)
    (hRc : ∀ Gs : Finset V.C, Gs.Nonempty → (∀ v ∈ Gs, 0 < w v) → ∀ h s,
      Rc h s (fun v => w v * (if v ∈ Gs then 1 else 0) / ∑ u ∈ Gs, w u) ≤ c / ∑ u ∈ Gs, w u) :
    ∃ q : Mixing V, feasibleMix V lam w q ∧
      ∀ s₁ : G.St 0, PhiR V π Rc q s₁ ≤ c * G.numStates := by sorry

end UninformedMG
