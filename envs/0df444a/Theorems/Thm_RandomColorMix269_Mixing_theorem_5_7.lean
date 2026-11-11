-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_theorem_5_7
-- name    : RandomColorMix269.Mixing.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:53.613732+00:00
-- url     : https://prove2.me/theorems/2dd248fc-aaf3-435c-9544-d67e7243cea3
-- title:
--   Theorem 5.7 — uniform block entropy factorization with $C_r\le((|V|-R_0)/(r-R_0))^{R_0}\le(2|V|/r)^{R_0}$
-- statement:
--   Let $\mu$ be a probability distribution on $\Omega\subseteq[q]^V$ that is $\gamma$-spectrally independent and $b$-marginally bounded ($b>0$) with connected conditional supports. Then for every $r=1,\dots,|V|$ there is $C_r>0$ such that for every $f\ge0$
--   $$
--   \frac r{|V|}\mathrm{Ent}_\mu[f]\le C_r\,\binom{|V|}r^{-1}\sum_{S\in\binom Vr}\mathrm{Ent}^S_\mu(f). \tag{10}
--   $$
--   Furthermore, if $r\ge2R_0$ with $R_0=\lceil4\gamma/b^2\rceil$, one can take
--   $$
--   C_r\le\Big(\frac{|V|-R_0}{r-R_0}\Big)^{R_0}\le\Big(\frac{2|V|}r\Big)^{R_0}.
--   $$
--   This is the global step of the entropy-factorization argument (Proposition 5.15).
--
--   Differences from the source:
--   - encoding: λ_max(Ψ^τ_µ) ≤ γ → z^T M z ≤ γ‖z‖² for M = D^{1/2} Ψ^τ_µ D^{-1/2}, D = diag of the one-site probabilities; reason: M is symmetric and similar to Ψ^τ_µ, so it has the same real spectrum; the empty matrix (all sites pinned) imposes nothing
--   - encoding: b-marginally bounded, with R₀ = ⌈4γ/b²⌉ → hypothesis 0 < b; reason: R₀ is undefined at b = 0; for b ≤ 0 marginal boundedness is empty
--   - encoding: distribution on Ω ⊆ [q]^V and f : Ω → ℝ≥0 → mass function on all of Fin q^V with support Ω, f ≥ 0 on all configurations; reason: values off the support do not enter any term
--   - encoding: there is C_r with (10); if r ≥ 2R₀ one can take C_r ≤ bound → one C_r > 0 satisfying (10) that, when 2R₀ ≤ r, is at most the bound; reason: equivalent because C_r is chosen after r
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.29, Theorem 5.7 (with Remark 5.8)

import Definitions.Def_RandomColorMix269_Mixing_Entropy

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Theorem 5.7, p.29, equation (10) and both explicit upper bounds.
Positive b is the domain of R₀ = ⌈4γ/b²⌉. -/
theorem theorem_5_7 {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (μ : (V → Fin q) → ℝ) (hμ : MarkovMixing.IsDist μ) (γ b : ℝ)
    (hb : 0 < b) (hSI : SpectralIndependent μ γ)
    (hMB : MarginalBounded μ b) (hCS : ConnectedConditionalSupports μ)
    (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ Fintype.card V) :
    ∃ Cr : ℝ, 0 < Cr ∧ BlockFactorization μ r Cr ∧
      (2 * Rzero γ b ≤ r →
        Cr ≤ factorBound (Fintype.card V) r (Rzero γ b) ∧
          factorBound (Fintype.card V) r (Rzero γ b) ≤
            (2 * (Fintype.card V : ℝ) / r) ^ (Rzero γ b)) := by sorry

end RandomColorMix269.Mixing
