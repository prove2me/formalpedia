-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_lemma_18
-- name    : UniversalNonstochastic.Main.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:39.758206+00:00
-- url     : https://prove2.me/theorems/6e11abec-5858-4eeb-aef4-b0f90a31d19d
-- title:
--   Lemma 18 — mass of a large complexity gap $K-F$ for divergent $F$
-- statement:
--   Let $K$ be prefix complexity and $\mathbf m$ a universal semimeasure, with tail $\tau$. Let $F:\mathbb N\to\mathbb N_0$ be an upper semicomputable function such that
--   $$\sum_{\omega}2^{-F(\omega)}=\infty .$$
--   Then there is a constant $c_4>0$ such that, for all $t\in\mathbb N_0$,
--   $$\mathbf m(\{\omega : K(\omega)-F(\omega)>t\})\;\ge\;c_4\,\tau(t). \tag{30}$$
--
--   The lemma applies to every such $F$, for example plain complexity $F=C$ or $F=0$. For $F=0$ it is the lower bound $\sigma\ge\tau/c$ of Lemma 4. In the proof of Theorem 10 it shows that objects with a large gap between $K$ and $F$ carry a tail's worth of universal mass.
--
--   **Formalization Note** The event $K(\omega)-F(\omega)>t$ is written $F(\omega)+t<K(\omega)$ in $\mathbb N_0\cup\{\infty\}$; this is the same event with signed subtraction. The divergence is the extended-nonnegative sum $\sum_\omega 2^{-F(\omega)}=\infty$.
--
--   Differences from the source:
--   - encoding: objects ω in a basic space 𝓧 in computable bijection with ℕ → objects are positive integers ℕ+ (the paper’s ℕ = {1,2,…}), coded by themselves; reason: the source explicitly permits replacing 𝓧 by ℕ in every formal statement (p.4); ObjectEncoding and the transport functions implement its fixed computable bijection without changing any instance
--   - encoding: K: prefix complexity defined by a fixed optimal decoder → U: an arbitrary optimal conditional prefix decoder; complexity is minimal halting-program length in ℕ∞, unconditional complexity uses condition 0; reason: the source fixes any optimal decoders; ℕ∞ is the exact infimum (⊤ only on no description, which optimality excludes); every statement is quantified over all such choices before its constants
--   - encoding: m: a fixed universal semimeasure on ℕ, m(A) = Σ_{a∈A} m(a) → m : UniversalSemimeasure (arbitrary), mass m A = real tsum of the indicator; reason: the weights are nonnegative with partial sums ≤ 1, so the real sum is the true sum; the statement is quantified over every universal semimeasure
--   - encoding: m({ω | K(ω) − F(ω) > t}) with signed difference → mass m {ω | F ω + t < K ω} in ℕ∞; reason: for integers K(ω) − F(ω) > t is equivalent to F(ω) + t < K(ω); no natural-number subtraction is used
--   - encoding: an upper semicomputable F with divergent nonnegative series Σω 2^(−F(ω)) = ∞ → REPred of the strict integer upper cuts and an ENNReal tsum equal to ⊤; reason: r.e. strict upper cuts give the source’s decreasing integer approximations, allowing initial ∞; ENNReal records genuine divergence, without the zero default of a nonsummable real tsum
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Lemma 18, eq. (30), p.16 (PDF p.16)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity

open scoped ENNReal

namespace UniversalNonstochastic.Main

/-- Lemma 18 (equation (30)), p.16: for every upper semicomputable `F : 𝓧 → ℕ₀` with
`∑_ω 2^{-F(ω)} = ∞` there is `c₄ > 0` with `m({ω | K(ω) - F(ω) > t}) ≥ c₄ τ(t)` for all
`t ∈ ℕ₀`. The event `K(ω) - F(ω) > t` is written `F(ω) + t < K(ω)`. -/
theorem lemma_18 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (F : ℕ+ → ℕ)
    (hF : IsUpperSemicomputableNat F) (hdiv : ∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω = ⊤) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ t : ℕ,
      c₄ * tail m (t : ℝ) ≤ mass m {ω | ((F ω + t : ℕ) : ℕ∞) < Kobj U ω} := by sorry

end UniversalNonstochastic.Main
