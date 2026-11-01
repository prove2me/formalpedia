-- Prove2me | Theorems.Thm_WildeQIT_Packing_eq_16_109
-- name    : WildeQIT.Packing.eq_16_109
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:25.752755+00:00
-- url     : https://prove2.me/theorems/df6df21d-0b0d-436d-9795-2c92a8d080e6
-- title:
--   Sequential decoding: $1-\mathbb E_{\mathcal C}\{\cdots\}\le2\sqrt{\varepsilon+2\sqrt\varepsilon+|\mathcal M|d/D}+\varepsilon$ (16.109)
-- statement:
--   **Sequential decoding bound, eq. (16.109).** Assume all the premises of the packing lemma (Lemma 16.3.1): an ensemble $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ of density operators on a finite-dimensional Hilbert space over a finite alphabet, with expected density operator $\sigma$, and orthogonal projectors $\Pi$, $\{\Pi_x\}$ with $\operatorname{Tr}\{\Pi\sigma_x\}\ge1-\varepsilon$, $\operatorname{Tr}\{\Pi_x\sigma_x\}\ge1-\varepsilon$, $\operatorname{Tr}\{\Pi_x\}\le d$ for every $x$ and $\Pi\sigma\Pi\le\frac1D\Pi$, where $\varepsilon\in(0,1)$, $D>0$, $d\in(0,D)$. Let the codewords $C_1,\dots,C_{|\mathcal M|}$ be drawn independently according to $p_X$, and write $\hat\Pi_x=I-\Pi_x$. Then the sequential decoder satisfies
--
--   $$1-\mathbb E_{\mathcal C}\Bigl\{\frac1{|\mathcal M|}\sum_m\operatorname{Tr}\bigl\{\Pi_{C_m}\hat\Pi_{C_{m-1}}\cdots\hat\Pi_{C_1}\Pi\sigma_{C_m}\Pi\hat\Pi_{C_1}\cdots\hat\Pi_{C_{m-1}}\Pi_{C_m}\bigr\}\Bigr\}\le2\sqrt{\varepsilon+2\sqrt\varepsilon+\frac{|\mathcal M|\,d}{D}}+\varepsilon .$$
--
--   It shows that a receiver who asks in turn "is it the first codeword?", "the second?", … decodes almost as well as with the square-root measurement of the packing lemma.
--
--   **Formalization Note** Messages are $\{0,\dots,M-1\}$ with $M\ge1$, tested in increasing order; the success probability of message $m$ is `WildeQIT.Packing.seqDecodeSuccess`. The expectation is the finite sum over codes weighted by $\prod_mp_X(c_m)$. Other conventions as in Lemma 16.3.1.
--
--   Differences from the source:
--   - encoding: a message set M of size |M| whose messages are tested in the order 1, …, |M| → Fin M with 0 < M; reason: the decoder needs an order, and the average 1/|M| Σ is undefined for an empty set
--   - encoding: E_C over the i.i.d. random code → finite sum Σ_c (∏_m p_X(c_m)) · (…); reason: this is the book's expectation (16.17)
--   - encoding: ΠσΠ ≤ (1/D)Π → ((1/D)Π − ΠσΠ).PosSemidef; reason: definition of the operator order
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §16.6, eq. (16.109), p. 502, under the premises of Lemma 16.3.1 (p. 498, "We begin with all of the objects and premises of the Packing Lemma"); decoder (16.82), p. 499

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_Packing_expectedState
import Definitions.Def_WildeQIT_Packing_codeProb
import Definitions.Def_WildeQIT_Packing_seqDecodeSuccess
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §16.6 (Sequential
Decoding), eq. (16.109), p. 502, under the premises of Lemma 16.3.1 (p. 498).
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Sequential decoding bound, eq. (16.109)** (Wilde, arXiv:1106.1445v8, §16.6, pp. 498–502).
Under all the premises of the packing lemma (Lemma 16.3.1: (16.11)–(16.14) with `ε ∈ (0, 1)`,
`D > 0`, `d ∈ (0, D)`) and with the codewords `C_1, …, C_{|ℳ|}` drawn independently according to
`p_X`, the sequential decoder (16.82) satisfies
`1 − E_C{(1/|ℳ|) ∑_m Tr{Π_{C_m} Π̂_{C_{m−1}} ⋯ Π̂_{C_1} Π σ_{C_m} Π Π̂_{C_1} ⋯ Π̂_{C_{m−1}} Π_{C_m}}}
≤ 2 √(ε + 2√ε + |ℳ| d / D) + ε`.

**Formalization Note.** Messages are `Fin M` with `0 < M` (the decoder tests the messages in
order); the success probability is `WildeQIT.Packing.seqDecodeSuccess`. Other conventions as in
`WildeQIT.Packing.lemma_16_3_1`. -/
theorem eq_16_109 {X n : Type} [Fintype X] [Fintype n] [DecidableEq n] {M : ℕ} (hM : 0 < M) (p : FinDist X) (σ : X → Matrix n n ℂ) (hσ : ∀ x, IsDensityOperator (σ x)) (P : Matrix n n ℂ) (Px : X → Matrix n n ℂ) (hP : IsStarProjection P) (hPx : ∀ x, IsStarProjection (Px x)) (ε D d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD : 0 < D) (hd0 : 0 < d) (hdD : d < D) (h11 : ∀ x, 1 - ε ≤ (P * σ x).trace.re) (h12 : ∀ x, 1 - ε ≤ (Px x * σ x).trace.re) (h13 : ∀ x, (Px x).trace.re ≤ d) (h14 : (((1 / D : ℝ) : ℂ) • P - P * expectedState p σ * P).PosSemidef) : 1 - ∑ c : Fin M → X, codeProb p c * ((M : ℝ)⁻¹ * ∑ m, seqDecodeSuccess P Px c m (σ (c m))) ≤ 2 * Real.sqrt (ε + 2 * Real.sqrt ε + (M : ℝ) * d / D) + ε := by sorry

end WildeQIT.Packing
