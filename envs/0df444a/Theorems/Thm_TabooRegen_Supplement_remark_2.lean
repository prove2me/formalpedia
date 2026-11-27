-- Prove2me | Theorems.Thm_TabooRegen_Supplement_remark_2
-- name    : TabooRegen.Supplement.remark_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:43:47.802301+00:00
-- url     : https://prove2.me/theorems/51d94e59-683d-4e47-84ef-1c0fab2aebf2
-- title:
--   Remark 2 — a classically regenerative process is taboo-regenerative in the wide sense, for every $A$
-- statement:
--   Let $S$ be a complete separable metric space and $A\subseteq S$ arbitrary. Suppose $X$ is **classically regenerative** (Definition 1) with respect to finite random times $0\le T'(0)<T'(1)<\cdots$: its cycles $W'_j$ are independent, and $W'_1,W'_2,\dots$ are identically distributed. Let $T(n)$ be the same times under the taboo convention, $T(n)=T'(n)$ on $\{T'(n)\le\Gamma\}$ and $T(n)=\infty$ otherwise, with cycles $W_n$. Then $X$ is **taboo-regenerative in the wide sense** (Definition 2) with respect to $(T(n))$: for every $n\ge0$,
--   $$
--   P\big((W_{n+1},W_{n+2},\dots)\in\cdot\mid T(0),\dots,T(n);\ \Gamma\ge T(n)\big)=P\big((W_1,W_2,\dots)\in\cdot\mid\Gamma\ge T(0)\big).
--   $$
--
--   No delay restriction, no assumption on $A$ and none of A1–A9 is needed. The remark lets every result for taboo-regenerative processes, in particular the exit-time asymptotics and the renewal arguments used for Theorem 3, be applied to classically regenerative processes.
--
--   Differences from the source:
--   - encoding: complete separable metric space $S$, paths in $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → Polish $S$ with its Borel σ-algebra; the published `Path S` (càdlàg maps into `S ⊕ Unit`, cylinder-trace σ-algebra); reason: the convention of the published `TabooRegen.Model`; the cylinder trace equals the Skorohod Borel σ-algebra for separable metric $\tilde S$
--   - reading: Definition 1 for the times $T(n)$ (no convention) and Definition 2 for times under the taboo convention $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → classical regeneration for finite times $T'(n)$ and wide-sense taboo regeneration (the published Definition 2) for their killed version $T(n)$; reason: the remark compares the two definitions for the same process, and p.275 imposes the taboo convention on the times of Definition 2; asking the killed cycles themselves to be i.i.d. would force $P(I_1=0)=0$
--   - encoding: independent and identically distributed random elements $W'_j$ of $D_{\tilde S}[0,\infty)$ → `iIndepFun` and `IdentDistrib` of measurable `Path S`-valued random elements carried with their defining equation; reason: cycles of càdlàg paths at measurable times are such random elements, so no instance changes
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Remark 2, p.275 (PDF p.5); Definition 1, p.273

import Mathlib
import Definitions.Def_TabooRegen_Supplement_Classical

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen.Supplement

open TabooRegen TabooRegen.Model

/-- **Remark 2** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing
Systems 46 (2004), p.275). Any classically regenerative process is automatically
taboo-regenerative in the wide sense (regardless of the choice of `A`).

**Formalization Note.** Classical regeneration (Definition 1, p.273) is `IsClassicallyRegen`: the
unkilled cycles `W′` are independent and `W′₁, W′₂, …` identically distributed, and the model's
times are their killed version under the taboo convention (p.275). Wide-sense taboo regeneration is
the published `IsWideSenseTabooRegen` (Definition 2) for the same model. `A` is arbitrary, a delay is
allowed, and none of A1–A9 is assumed. `S` is Polish with its Borel σ-algebra (the paper's standing
assumption, p.272). -/
theorem remark_2 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hcl : IsClassicallyRegen M) : M.IsWideSenseTabooRegen := by sorry

end TabooRegen.Supplement
