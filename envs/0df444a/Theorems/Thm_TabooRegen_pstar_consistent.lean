-- Prove2me | Theorems.Thm_TabooRegen_pstar_consistent
-- name    : TabooRegen.pstar_consistent
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:29.348474+00:00
-- url     : https://prove2.me/theorems/111975c4-d76b-49a6-bb2a-b3b4a74d2531
-- title:
--   p.285 — the taboo limit $P^*$ is a consistently defined probability (window laws)
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense and satisfy A1 and A4 (a delay is allowed). For every $k\ge0$:
--
--   1. the window law $B\mapsto P^*\big(((W_j:|j|\le k),\beta)\in B\big)$ on $D_{\tilde S}^{\,2k+1}\times\mathbb R$ is a probability measure;
--   2. the window law for $k+1$, restricted to the middle $2k+1$ cycles and the age, is the window law for $k$.
--
--   Together these say that $P^*$ consistently defines a joint probability on $(W,\beta)$. The paper notes that the central point is that A1 makes the change of measure $L(-n)$ a martingale in $n$, and (Remark 14) that A1 and A4 alone suffice; A3 is not needed.
--
--   Differences from the source:
--   - reading: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ and $P^*$ → under the cycle law $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: in the delayed case the unconditioned law of $W_1$ also contains junk cycles after an exit during the delay; by Definition 2 ($n=0$) $Q$ is the law of the non-delayed version, and $Q=P$ when $T(0)=0$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $P^*$, a probability on the bi-infinite $(W,\beta)$ defined by (4.1) and the change of measure of p.285 → its window laws `PstarWindow k`, the explicit formula obtained from (4.1) and p.285 with $n=k$; reason: the statement involves only finite windows
--   - encoding: $P^*$ consistently defines a joint probability on $(W,\beta)$ → every window law is a probability measure and the window laws are consistent under dropping the two outer cycles; reason: for standard Borel path spaces this is equivalent by the Kolmogorov extension theorem
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, p.285 (PDF p.15), "it is easily shown that P∗ consistently defines a joint probability on (W, β)"; Remark 14, p.288

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **`P*` is consistently defined** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), p.285: "it is easily shown that `P∗`
consistently defines a joint probability on `(W, β)`"; Remark 14, p.288: "only A1 and A4 are
required in order that `P∗` be unambiguousily defined as a probability").
Under Definition 2, A1 and A4, for every `k`:
1. the window law `P*_k` of `((W_j : |j| ⩽ k), β)` is a probability measure;
2. `P*_{k+1}`, restricted to the middle `2k + 1` cycles and the age, is `P*_k`.

**Formalization Note.** The delay is allowed; the cycle quantities are under `Q = P(· | Γ ⩾ T(0))`.
`P*` is represented by its finite window laws `PstarWindow`. -/
theorem pstar_consistent {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h4 : M.A4 α) (k : ℕ) :
    (∃ μ : Measure ((Fin (2 * k + 1) → Path S) × ℝ), IsProbabilityMeasure μ ∧
        ∀ B, MeasurableSet B → μ B = M.PstarWindow α k B) ∧
      ∀ B : Set ((Fin (2 * k + 1) → Path S) × ℝ), MeasurableSet B →
        M.PstarWindow α (k + 1) ((fun p => (dropOuter k p.1, p.2)) ⁻¹' B) =
          M.PstarWindow α k B := by sorry

end TabooRegen
