-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_theorem_10
-- name    : UniversalNonstochastic.Main.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:08:24.779548+00:00
-- url     : https://prove2.me/theorems/445a3fc2-7481-4b48-b820-4ba58f2b0326
-- title:
--   Theorem 10 — deficiencies dominating $d_F$ have abundant non-quasi-stochastic objects
-- statement:
--   Fix prefix complexity $K$ and a universal semimeasure $\mathbf m$ on the positive integers, with tail $\tau(t)=\mathbf m(\{n:n>t\})$. Let $d$ be a deficiency (a lower semicomputable function $d(\omega\mid Q)\in(-\infty,\infty]$ of an object and an elementary probability measure). Let $F:\mathbb N\to\mathbb N_0$ be an upper semicomputable function with $\sum_\omega 2^{-F(\omega)}=\infty$, and let $d_F(\omega\mid Q)=-\log_2 Q(\{\omega\})-F(\omega)$, with $-\log_2 0=\infty$. Suppose there is a constant $c>0$ such that
--   $$d_F(\omega\mid Q)\le c\,d(\omega\mid Q)+c \tag{13}$$
--   for all objects $\omega$ and all elementary probability measures $Q$. Then there exists $c'>0$ such that
--   $$\mathbf m(N_{\alpha,\beta}(d))\;\ge\;\tau(\max(\alpha,\beta))/c'\qquad\text{for all }\alpha\in\mathbb N_0\text{ and }\beta\in[0,\infty).$$
--   Here $N_{\alpha,\beta}(d)$ is the set of objects $\omega$ for which no elementary $Q$ has $K(Q)\le\alpha$ and $d(\omega\mid Q)\le\beta$.
--
--   This is the general lower-bound criterion used for finite-set stochasticity in Section A.2. Its scope includes every deficiency satisfying (13), without a calibration assumption.
--
--   **Formalization Note** Inequality (13) is evaluated in the extended reals; since $c>0$, $c\cdot(+\infty)+c=+\infty$.
--
--   Differences from the source:
--   - encoding: objects ω in a basic space 𝓧 in computable bijection with ℕ → objects are positive integers ℕ+ (the paper’s ℕ = {1,2,…}), coded by themselves; reason: the source explicitly permits replacing 𝓧 by ℕ in every formal statement (p.4); ObjectEncoding and the transport functions implement its fixed computable bijection without changing any instance
--   - encoding: K: prefix complexity defined by a fixed optimal decoder → U: an arbitrary optimal conditional prefix decoder; complexity is minimal halting-program length in ℕ∞, unconditional complexity uses condition 0; reason: the source fixes any optimal decoders; ℕ∞ is the exact infimum (⊤ only on no description, which optimality excludes); every statement is quantified over all such choices before its constants
--   - encoding: m: a fixed universal semimeasure on ℕ, m(A) = Σ_{a∈A} m(a) → m : UniversalSemimeasure (arbitrary), mass m A = real tsum of the indicator; reason: the weights are nonnegative with partial sums ≤ 1, so the real sum is the true sum; the statement is quantified over every universal semimeasure
--   - encoding: an upper semicomputable F with divergent nonnegative series Σω 2^(−F(ω)) = ∞ → REPred of the strict integer upper cuts and an ENNReal tsum equal to ⊤; reason: r.e. strict upper cuts give the source’s decreasing integer approximations, allowing initial ∞; ENNReal records genuine divergence, without the zero default of a nonsummable real tsum
--   - encoding: a lower semicomputable deficiency valued in (−∞,∞], satisfying (13), and β ∈ [0,∞) → IsDeficiency excludes ⊥ and has uniformly r.e. rational strict lower cuts; (13) uses EReal arithmetic, and β is real with 0 ≤ β; reason: these are the same effective and extended-real conventions; positive c makes c·⊤ + c = ⊤, and β remains finite as in the source
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Theorem 10, eq. (13), p.11 (PDF p.11); proof Sect. A.6 p.22

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels

open scoped ENNReal

namespace UniversalNonstochastic.Main

/-- Theorem 10, p.11: let `d` be a deficiency and `F : 𝓧 → ℕ₀` upper semicomputable with
`∑_ω 2^{-F(ω)} = ∞`. If `d_F(ω | Q) ≤ c d(ω | Q) + c` (13) for some `c > 0`, all `ω` and all
elementary `Q`, then `m(N_{α,β}(d)) ≥ τ(max(α, β))/c'` for some `c' > 0`, all `α ∈ ℕ₀`
and all `β ∈ [0, ∞)`. -/
theorem theorem_10 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder)
    (d : ℕ+ → ElemMeasure → EReal) (hd : IsDeficiency d)
    (F : ℕ+ → ℕ) (hF : IsUpperSemicomputableNat F)
    (hdiv : ∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω = ⊤)
    (h13 : ∃ c : ℝ, 0 < c ∧ ∀ (ω : ℕ+) (Q : ElemMeasure),
      dF F ω Q ≤ ((c : ℝ) : EReal) * d ω Q + ((c : ℝ) : EReal)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      tail m (max (α : ℝ) β) / c' ≤ mass m (nonQuasiStochastic U d α β) := by sorry

end UniversalNonstochastic.Main
