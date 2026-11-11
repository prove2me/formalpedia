-- Prove2me | Theorems.Thm_PreservePast_lemma_1
-- name    : PreservePast.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:37.654959+00:00
-- url     : https://prove2.me/theorems/296b831e-acbd-423d-bc10-add5cdb40db2
-- title:
--   Lemma 1 — fixed-action events and arbitrary messages
-- statement:
--   Let $(\Omega,P)$ be a probability space, $V$ a random history (in a standard Borel space) independent of the public randomness $\mathcal U$, and $M$ a $B$-bit message (at most $2^B$ values), jointly randomized in any way. Write $I(V;M\mid\mathcal U)$ for the conditional mutual information in bits, and compare the actual law of $(\mathcal U,V,M)$ with the reference law that makes $V$ independent of $M$ conditional on $\mathcal U$.
--
--   1. $I(V;M\mid\mathcal U)\le B$, and if an event has actual probability $s$ and reference probability at most $p$, $0<p<1$, then
--   $$
--   B\ \ge\ I(V;M\mid\mathcal U)\ \ge\ s\log_2(1/p)-1 .
--   $$
--   2. If moreover $p<s$, then $I(V;M\mid\mathcal U)\ge\mathrm{kl}_2(s\|p)$.
--   3. Let $Y$ be a history block and $C$ a context variable (the paper's $H_i$ and $C=(\mathcal U,H_{<i})$). Suppose that for every message $m$ the set $E_m(c)$ selected for the response in context $c$ has conditional prior mass $\Pr\{Y\in E_m(c)\mid C=c\}\le e^{-A(c)}$, where $A\ge0$, and let $s(c)=\Pr\{Y\in E_M(c)\mid C=c\}$ be the actual conditional membership probability. Then
--   $$
--   I(Y;M\mid C)\ \ge\ \mathbb E\Big[\frac{s(C)A(C)}{\ln2}-h_2(s(C))\Big].
--   $$
--   4. The chain rule: for a history $H=(H_1,\dots,H_k)$, $I(H;M\mid\mathcal U)=\sum_{i=1}^kI(H_i;M\mid\mathcal U,H_{<i})$, which adds the component bounds of part 3.
--
--   Lemma 1 charges the compatible-mass bounds of Theorem 1 against arbitrary randomized messages, including several history blocks under one joint message.
--
--   **Formalization Note** The decoder's output is a function of $(M,\mathcal U)$ once its coins are part of $\mathcal U$, so an event about the response is an event on $(\mathcal U,V,M)$ and the reference law uses the same decoder channel. Part 3 is written as $\mathbb E[sA/\ln2]\le I+\mathbb E[h_2(s)]$ with lower integrals ($0\le h_2\le1$), which needs no integrability side condition.
--
--   Differences from the source:
--   - encoding: an event about the decoder's response, under the actual and reference laws with the same decoder channel → a measurable event on (𝒰, V, M), the decoder's coins being part of 𝒰; reason: the response is a function of (M, 𝒰); same instances
--   - generalization: part (3) for the context C = (𝒰, H_{<i}) → part (3) for an arbitrary context variable C and block Y; reason: the paper's context is one instance
--   - generalization: conditional prior mass at most e^{−A_i(C)} for every fixed response → the bound required for every message and almost every context value; reason: weaker hypothesis; the paper's 'every' implies 'almost every'
--   - encoding: I(H_i; M | C) ≥ 𝔼[s_i A_i/ln 2 − h₂(s_i)] → 𝔼[s A/ln 2] ≤ I + 𝔼[h₂(s)] with lower integrals; reason: equivalent since 0 ≤ h₂ ≤ 1; avoids junk Bochner integrals
--   - reading: 'The information chain rule adds these component bounds' → the identity I(H; M | 𝒰) = Σ_i I(H_i; M | 𝒰, H_{<i}); reason: the sentence invokes the chain rule; stated as the identity it refers to
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2.1, p.3 (PDF p.5), Lemma 1, (3)

import Mathlib
import Definitions.Def_PreservePast_cmiBits

open MeasureTheory ProbabilityTheory

namespace PreservePast

/-- **Lemma 1 (fixed-action events and arbitrary messages).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2.1, p.3 (PDF p.5): "Let V
be independent of public randomness 𝒰. Given 𝒰, a B-bit message has at most 2^B values. Compare the
actual joint law with the law making V independent of M conditional on 𝒰, using the same decoder
channel. If an event has actual probability s and reference probability at most p, 0 < p < 1, then
B ≥ I(V; M | 𝒰) ≥ s log₂(1/p) − 1. For p < s, also I(V; M | 𝒰) ≥ kl₂(s‖p). More generally, put
C = (𝒰, H_{<i}) and suppose a selected compatible set for H_i has conditional prior mass at most
e^{−A_i(C)}, A_i(C) ≥ 0, for every fixed response. If its actual conditional membership probability
is s_i(C), then I(H_i; M | C) ≥ 𝔼[s_i(C)A_i(C)/ln 2 − h₂(s_i(C))]. (3) The information chain rule
adds these component bounds."

Four parts, for a probability space `(Ω, P)` and a message `M ∈ {0, …, 2^B − 1}`:
1. `I(V; M | 𝒰) ≤ B`, and for every measurable event on `(𝒰, V, M)` with actual probability `s`
   and reference probability at most `p ∈ (0, 1)`, `I(V; M | 𝒰) ≥ s log₂(1/p) − 1`;
2. if moreover `p < s`, then `I(V; M | 𝒰) ≥ kl₂(s‖p)`;
3. (3), for a block `Y` (the paper's `H_i`) and a context `C` (the paper's `(𝒰, H_{<i})`): if the
   set `E_m(c)` selected for message `m` in context `c` has conditional prior mass at most
   `e^{−A(c)}` for every `m`, and `s(c)` is the conditional probability that `Y ∈ E_M(c)`, then
   `I(Y; M | C) ≥ 𝔼[s(C)A(C)/ln 2 − h₂(s(C))]`;
4. the chain rule `I(H; M | 𝒰) = Σ_i I(H_i; M | 𝒰, H_{<i})` for a history `H = (H_0, …, H_{k−1})`.

**Formalization Note.** `I` is `cmiBits` (bits, `ℝ≥0∞`). The reference law is `refLaw`: the
joint law of `(𝒰, (V, M))` with `V` and `M` made conditionally independent given `𝒰`. The decoder's
response is a function of `(M, 𝒰)` once the decoder's coins are included in `𝒰`, so an event about
the response is an event on `(𝒰, V, M)` and the same decoder channel is used under both laws. A
selected set depends on the response, hence on `(m, c)`; `C` is an arbitrary random variable.
Part 3 is stated as `𝔼[sA/ln 2] ≤ I + 𝔼[h₂(s)]` with lower integrals (`0 ≤ h₂ ≤ 1`), which is the
paper's inequality and needs no integrability side condition. In part 4, `H_{<i}` is the tuple
`(H_j)_{j<i}`. -/
theorem lemma_1 {Ω 𝒱 𝒰 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒱] [StandardBorelSpace 𝒱]
    [Nonempty 𝒱] [MeasurableSpace 𝒰] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ)
    (V : Ω → 𝒱) (U : Ω → 𝒰) (M : Ω → Fin (2 ^ B)) (hV : Measurable V) (hU : Measurable U)
    (hM : Measurable M) (hind : IndepFun V U P) :
    cmiBits P V M U ≤ (B : ENNReal) ∧
    (∀ (E : Set (𝒰 × (𝒱 × Fin (2 ^ B)))) (p : ℝ), MeasurableSet E →
      refLaw P V M U E ≤ ENNReal.ofReal p → 0 < p → p < 1 →
      let s : ℝ := (P.map (fun ω => (U ω, (V ω, M ω))) E).toReal
      ENNReal.ofReal (s * Real.logb 2 (1 / p) - 1) ≤ cmiBits P V M U ∧
        (p < s → ENNReal.ofReal (kl2 s p) ≤ cmiBits P V M U)) ∧
    (∀ {𝒴 𝒞 : Type*} [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
      [MeasurableSpace 𝒞] (Y : Ω → 𝒴) (C : Ω → 𝒞) (A : 𝒞 → ℝ)
      (Esel : Fin (2 ^ B) → 𝒞 → Set 𝒴),
      Measurable Y → Measurable C → Measurable A → (∀ c, 0 ≤ A c) →
      MeasurableSet {q : 𝒞 × (𝒴 × Fin (2 ^ B)) | q.2.1 ∈ Esel q.2.2 q.1} →
      (∀ m, ∀ᵐ c ∂(P.map C), condDistrib Y C P c (Esel m c) ≤ ENNReal.ofReal (Real.exp (-A c))) →
      let s : 𝒞 → ℝ := fun c =>
        (condDistrib (fun ω => (Y ω, M ω)) C P c {q | q.1 ∈ Esel q.2 c}).toReal
      ∫⁻ c, ENNReal.ofReal (s c * A c / Real.log 2) ∂(P.map C) ≤
        cmiBits P Y M C + ∫⁻ c, ENNReal.ofReal (h2 (s c)) ∂(P.map C)) ∧
    (∀ {𝒴 : Type*} [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴] (k : ℕ)
      (H : Ω → Fin k → 𝒴), Measurable H →
      cmiBits P H M U = ∑ i : Fin k, cmiBits P (fun ω => H ω i) M
        (fun ω => (U ω, fun j : Fin i => H ω ⟨j, lt_trans j.isLt i.isLt⟩))) := by sorry

end PreservePast
