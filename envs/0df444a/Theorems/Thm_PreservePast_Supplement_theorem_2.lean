-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_2
-- name    : PreservePast.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:32:40.223803+00:00
-- url     : https://prove2.me/theorems/0febd6d1-7a1f-494a-8f6e-a2ba491cba95
-- title:
--   Theorem 2 — exact compatible mass and group-symmetric response codes
-- statement:
--   Let $\mathcal T$ be a nonempty compact metric space of histories with prior $\mu$, and $\mathcal B$ a nonempty compact convex subset of a Hausdorff locally convex space. For scores $g_h(z)$ with values $V(h)=\sup_{z\in\mathcal B}g_h(z)$, suppose the score loss $d_h(z)=V(h)-g_h(z)$ is nonnegative, jointly continuous, and convex in $z$. For $b\ge0$ put
--   $$E_z(b)=\{h\in\mathcal T:\ d_h(z)\le b\},\qquad p_b=\max_{z\in\mathcal B}\mu(E_z(b)).$$
--
--   1. The maximum is attained, and the finite-order source exponent $\mathcal H_n(b;\mu)$ (the published `PreservePast.sourceExp`) satisfies
--   $$\mathcal H_\infty(b;\mu):=\lim_{n\to\infty}\mathcal H_n(b;\mu)=-\ln p_b .$$
--   2. Suppose further that $\mu(\mathcal T)=1$ and a compact group $\mathcal G$ acts continuously and transitively on $\mathcal T$, preserves $\mu$ and the score losses ($d_{\gamma h}(\gamma z)=d_h(z)$), and acts continuously on $\mathcal B$. Then for every $s\in(0,1)$, if $p_b>0$, there is a query-blind public-coin code with
--   $$B\le\frac{\mathcal H_\infty(b;\mu)}{\ln 2}+\log_2\Big(1+\ln\frac1{1-s}\Big)+1$$
--   bits which, for every fixed history $h$, selects with probability at least $s$ an action $z$ with $h\in E_z(b)$.
--
--   The first part says that testing finite subtuples recovers the largest prior mass served by one action; the second turns that mass into a finite response code.
--
--   **Formalization Note** $-\ln p_b$ is an extended real ($+\infty$ if $p_b=0$). The code is a coin space, an encoder $\mathcal T\to\Omega\to\{1,\dots,2^B\}$ and a Borel-measurable selection of an action from the message and the coins.
--
--   Differences from the source:
--   - encoding: μ is a prior on histories and 𝒯 a compact domain (possibly a typical subset), with μ(𝒯) = 1 only in the second part → the history type is 𝒯 and μ is a Borel measure on it of mass ≤ 1 (mass 1 in the second part); the source exponent is taken with domain the whole type; reason: W_n(b) ⊆ 𝒯ⁿ, so only the restriction of the prior to 𝒯 enters definition (2)
--   - encoding: if each z measurably realizes a complete legal policy succeeding on E_z(b), a query-blind public-coin code succeeds with probability at least s for every fixed history → the code measurably selects an action z from the message and the coins, and h ∈ E_z(b) with probability at least s; reason: executing the policy realized by the selected z then succeeds on every query, and for the realization in which the policy of z is z the two statements coincide
--   - encoding: a compact group → a compact Hausdorff topological group; reason: the usual meaning of compact group
--   - encoding: p_b = max_z μ(E_z(b)) → the supremum over z together with the assertion that it is attained; reason: states the maximum without choosing a maximizer
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 2, p.3 (PDF p.5), eqs. (5)–(6); Lemma 3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PreservePast_sourceExp

open MeasureTheory Filter Topology

namespace PreservePast.Supplement

/-- **Theorem 2 (Exact compatible mass and group-symmetric response codes).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 2,
p.3 (PDF p.5), eqs. (5)–(6); the code is that of Lemma 3, p.14 (PDF p.16).

`𝒯` is a nonempty compact metric space, `𝓑` a nonempty compact convex subset of a Hausdorff
locally convex space `E`, and `d_h(z) = V(h) − g_h(z)` is nonnegative, jointly continuous and
convex in `z`. With `E_z(b) = {h ∈ 𝒯 : d_h(z) ≤ b}` and `p_b = max_z μ(E_z(b))`:
(5) the maximum is attained and `lim_n 𝓗_n(b; μ) = −ln p_b` for every `b ≥ 0`;
(6) if moreover `μ(𝒯) = 1` and a compact group `𝒢` acts continuously and transitively on `𝒯`,
preserves `μ` and the score losses, and acts continuously on `𝓑`, then for every `s ∈ (0,1)` and
`p_b > 0` there is a query-blind public-coin code of
`B ≤ 𝓗_∞(b; μ)/ln 2 + log₂(1 + ln(1/(1−s))) + 1` bits that succeeds with probability at least `s`
for every fixed history.

**Formalization Note.** The history type `Θ` is `𝒯` itself and `μ` is the restriction of the
prior to `𝒯`: a Borel measure of total mass `≤ 1` in (5) (the published `sourceExp` is evaluated
with domain `Set.univ`; `W_n(b) ⊆ 𝒯ⁿ`, so only this restriction enters (2)) and of mass `1` in
(6). The scores are `g : Θ → E → ℝ`, restricted to the subtype `𝓑`, so that the published
`optVal` is `V(h) = sup_{z∈𝓑} g_h(z)`; nonnegativity of `d` makes this a genuine supremum.
`−ln p_b` is `-ENNReal.log p_b ∈ EReal` (`+∞` when `p_b = 0`). The group acts on the subtype
`𝓑`; a compact group is taken Hausdorff, as usual. The code is a coin space, an encoder
`𝒯 → Ω → Fin (2^B)` and a decoder selecting an action `z ∈ 𝓑` from the message and the coins (Borel measurably in the coins); it
succeeds on `h` when `h ∈ E_z(b)` for the selected `z`. By the hypothesis "each z ∈ 𝓑 measurably
realizes a complete legal policy succeeding on E_z(b)", executing the policy of the selected `z`
then succeeds on every query, so this is the source's conclusion for every such realization, and
it is the conclusion itself for the realization in which the policy of `z` is `z`. -/
theorem theorem_2 {Θ E : Type} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (𝓑 : Set E) (h𝓑c : IsCompact 𝓑) (h𝓑v : Convex ℝ 𝓑) (h𝓑n : 𝓑.Nonempty)
    (g : Θ → E → ℝ) (μ : Measure Θ) (hμ : μ Set.univ ≤ 1)
    (hnonneg : ∀ (h : Θ) (z : 𝓑), 0 ≤ optVal (fun h (z : 𝓑) => g h z) h - g h z)
    (hcont : Continuous fun q : Θ × 𝓑 => optVal (fun h (z : 𝓑) => g h z) q.1 - g q.1 q.2)
    (hconv : ∀ h : Θ, ConvexOn ℝ 𝓑 fun z => optVal (fun h (z : 𝓑) => g h z) h - g h z)
    (b : ℝ) (hb : 0 ≤ b) :
    ((∃ z₀ : 𝓑, μ {h | optVal (fun h (z : 𝓑) => g h z) h - g h z₀ ≤ b} =
          ⨆ z : 𝓑, μ {h | optVal (fun h (z : 𝓑) => g h z) h - g h z ≤ b}) ∧
      Tendsto (fun n : ℕ => sourceExp (fun h (z : 𝓑) => g h z) Set.univ μ n b) atTop
        (𝓝 (-ENNReal.log (⨆ z : 𝓑, μ {h | optVal (fun h (z : 𝓑) => g h z) h - g h z ≤ b})))) ∧
    ∀ (𝒢 : Type) [Group 𝒢] [TopologicalSpace 𝒢] [IsTopologicalGroup 𝒢] [CompactSpace 𝒢]
      [T2Space 𝒢] [MulAction 𝒢 Θ] [ContinuousSMul 𝒢 Θ] [MulAction.IsPretransitive 𝒢 Θ]
      [MulAction 𝒢 𝓑] [ContinuousSMul 𝒢 𝓑],
      μ Set.univ = 1 → (∀ γ : 𝒢, μ.map (fun h => γ • h) = μ) →
      (∀ (γ : 𝒢) (h : Θ) (z : 𝓑), optVal (fun h (z : 𝓑) => g h z) (γ • h) - g (γ • h) ((γ • z : 𝓑) : E) =
        optVal (fun h (z : 𝓑) => g h z) h - g h z) →
      ∀ s : ℝ, 0 < s → s < 1 →
        0 < (⨆ z : 𝓑, μ {h | optVal (fun h (z : 𝓑) => g h z) h - g h z ≤ b}) →
        ∃ B : ℕ, (B : ℝ) ≤
            -Real.log (⨆ z : 𝓑, μ {h | optVal (fun h (z : 𝓑) => g h z) h - g h z ≤ b}).toReal /
                Real.log 2 + Real.logb 2 (1 + Real.log (1 / (1 - s))) + 1 ∧
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (enc : Θ → Ω → Fin (2 ^ B))
            (sel : Fin (2 ^ B) → Ω → 𝓑),
            IsProbabilityMeasure P ∧ (∀ h, Measurable (enc h)) ∧ (∀ M, @Measurable Ω 𝓑 _ (borel 𝓑) (sel M)) ∧
            ∀ h : Θ, ENNReal.ofReal s ≤
              P {ω | optVal (fun h (z : 𝓑) => g h z) h - g h (sel (enc h ω) ω) ≤ b} := by sorry

end PreservePast.Supplement
