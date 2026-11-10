-- Prove2me | Theorems.Thm_QPSpinProfile_lemma_2_6
-- name    : QPSpinProfile.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:28:07.228423+00:00
-- url     : https://prove2.me/theorems/90ac34d0-d74c-4b85-add8-00cc5255aa63
-- title:
--   Lemma 2.6: profile entropy and benchmark comparison
-- statement:
--   Fix $n\ge p\ge2$. Let $\mathcal C_n$ and $\mathcal B_n$ be classes of $n$-qubit states, let $0\le m_\star\le n-p$ be an integer and $r>0$. Suppose every $\rho\in\mathcal C_n$ admits $J\in\mathcal J_{n,m_\star}$ and $\sigma\in\mathrm{conv}(\mathcal B_n)$ with $\|M_J(f_\rho-f_\sigma)\|_{n,p}\le r$. Then
--   $$
--   \mathbb E\,\Delta^{\mathrm{ref}}_{n,p}(\mathcal C_n;\mathcal B_n)\le C\int_0^{2r}\sqrt{\log\big(2|\mathcal J_{n,m_\star}|\,N(\varepsilon,F_{n,p}(\mathcal C_n),\|\cdot\|_{n,p})\big)}\,d\varepsilon+C\,3^{p/2}\sqrt{p\,m_\star}, \tag{23}
--   $$
--   and for every $t>0$,
--   $$
--   \mathbb P\Big(\Delta^{\mathrm{ref}}_{n,p}(\mathcal C_n;\mathcal B_n)\ge\mathbb E\,\Delta^{\mathrm{ref}}_{n,p}(\mathcal C_n;\mathcal B_n)+t\Big)\le\exp\Big(-\frac{t^2}{8\cdot3^p}\Big). \tag{24}
--   $$
--   Here $C$ is a universal constant.
--
--   The lemma converts local profile complexity into an energy bound relative to a benchmark; both parts of Theorem 1.2 are derived from it.
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: standing assumption (p.3): all state classes are nonempty → explicit hypotheses that each class is nonempty and consists of density operators; reason: the paper's standing assumption made explicit; it also keeps the real suprema $E_{n,p}$ meaningful
--   - reading: the constant $C$ of (23), written without a quantifier → one universal constant chosen before $n$, $p$, the classes and $r$; reason: the paper's convention for $C$ in §2, and the proof (Dudley's constant and Lemma 2.5's) gives a universal constant; this is the stronger reading
--   - encoding: $\mathbb E\,\Delta^{\mathrm{ref}}$ and the entropy integral in (23) → lower Lebesgue integrals in $[0,\infty]$; the integrand is $\infty$ where $N=\infty$; reason: both integrands are nonnegative; no integrability condition is hidden
--   - encoding: $\mathbb E\,\Delta^{\mathrm{ref}}$ in (24), a finite number → Bochner integral, with integrability of $\Delta^{\mathrm{ref}}$ asserted as a conclusion; reason: the paper's finite expectation presupposes integrability; asserting it excludes the junk value $0$
--   - encoding: $3^{p/2}$; $0\le m_\star\le n-p$ for integers → $(\sqrt3)^p$; $p\le n$ and $m_\star\le n-p$ in $\mathbb N$; reason: equal; same range
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Lemma 2.6, p.23 (PDF p.26), displays (23), (24)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QPSpinProfile_profile
import Definitions.Def_QPSpinProfile_coverNum
import Definitions.Def_QPSpinProfile_maxEnergy
import Definitions.Def_QPSpinProfile_Hhit

namespace QPSpinProfile

open MeasureTheory

/-- **Lemma 2.6 (Profile entropy and benchmark comparison)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.23, PDF p.26).
Fix `n ≥ p ≥ 2`, classes `C_n`, `B_n` of `n`-qubit states, an integer `0 ≤ m⋆ ≤ n − p` and
`r > 0`. If every `ρ ∈ C_n` has `J ∈ J_{n,m⋆}` and `σ ∈ conv(B_n)` with
`‖M_J(f_ρ − f_σ)‖_{n,p} ≤ r`, then (23)
`E Δ^ref ≤ C ∫_0^{2r} √(log(2|J_{n,m⋆}| N(ε, F_{n,p}(C_n), ‖·‖_{n,p}))) dε + C 3^{p/2} √(p m⋆)`,
and (24) `P(Δ^ref ≥ E Δ^ref + t) ≤ exp(−t²/(8·3^p))` for every `t > 0`.

**Formalization Note** `C` is universal (quantified first). In (23) the expectation of the
nonnegative `Δ^ref` and the entropy integral are lower Lebesgue integrals in `[0, ∞]`; the
integrand is `∞` where `N = ∞`. In (24) the centring `E Δ^ref` is a Bochner integral and the
statement asserts integrability of `Δ^ref` as well. The classes are nonempty sets of states (the
paper's standing assumption, p.3). -/
theorem lemma_2_6 : ∃ C : ℝ, 0 < C ∧
    ∀ (n p m : ℕ) (Cn Bn : Set (Matrix (Qubits n) (Qubits n) ℂ)) (r : ℝ),
      2 ≤ p → p ≤ n → m ≤ n - p → 0 < r →
      Cn.Nonempty → (∀ ρ ∈ Cn, WildeQIT.IsDensityOperator ρ) →
      Bn.Nonempty → (∀ σ ∈ Bn, WildeQIT.IsDensityOperator σ) →
      (∀ ρ ∈ Cn, ∃ J ∈ admissible n m, ∃ σ ∈ convexHull ℝ Bn,
        profileNorm (coordProj J (profile p ρ - profile p σ)) ≤ r) →
      (∫⁻ g, ENNReal.ofReal (deltaRef n p Cn Bn g) ∂(gaussMeasure n p)
          ≤ ENNReal.ofReal C *
              ∫⁻ ε in Set.Ioc 0 (2 * r),
                (if coverNum ε (profileClass n p Cn) = ⊤ then ⊤ else
                  ENNReal.ofReal (Real.sqrt (Real.log
                    (2 * ((admissible n m).card : ℝ) * ((coverNum ε (profileClass n p Cn)).toNat : ℝ)))))
            + ENNReal.ofReal (C * Real.sqrt 3 ^ p * Real.sqrt ((p : ℝ) * m))) ∧
      Integrable (deltaRef n p Cn Bn) (gaussMeasure n p) ∧
      ∀ t : ℝ, 0 < t →
        gaussMeasure n p
            {g | (∫ g', deltaRef n p Cn Bn g' ∂(gaussMeasure n p)) + t ≤ deltaRef n p Cn Bn g}
          ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (8 * 3 ^ p))) := by sorry

end QPSpinProfile
