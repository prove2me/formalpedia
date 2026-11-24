-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_Supplement_theorem_6
-- name    : SmithRegenerative.Moments.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:49:24.731275+00:00
-- url     : https://prove2.me/theorems/2e62e4dd-6c1f-47db-aa65-bbcfe138e8fe
-- title:
--   Theorem 6 — S.M. insensitivity (corrected: aperiodicity and completion)
-- statement:
--   Consider two regular S.M. realizations freshly entering the same initial label $z$. Fix a state $\mu$ whose return law is aperiodic in both models. Assume equality of transition probabilities for every pair of states, and equality of finite wait masses and of extended wait means for every pair $(\lambda,\nu)$ at which $\Omega_{\lambda\nu}$ is defined: the diagonal (unconditional) laws and every pair with $p_{\lambda\nu}\ne0$. If the unconditional mean wait in $\mu$ is finite in either model, there is a common real limit $L$ such that
--   $$\lim_{t\to\infty}P_z(x_t^{(1)}=\mu)=L=\lim_{t\to\infty}P_z(x_t^{(2)}=\mu).$$
--   This retains both existence and equality, all five numbered source premises, and equality of infinite means as well as finite ones. No coupling of the two processes is required. The result expresses insensitivity to waiting-time shapes under the stated matching data.
--
--   Differences from the source:
--   - correction: The entry event is “not periodic”. → The return law is aperiodic.; reason: Section 3·3 says the joint event-period and aperiodicity cases are not exhaustive. Return span 2 and first delay 1 satisfy the literal printed premise but give oscillating occupation. The proof invokes Corollary 2·1, which requires an aperiodic cycle law. Excluded cases are lattice return laws with misaligned delay spans; see DISPROOF.md.
--   - correction: A positive-integer state process; the text asserts that its regularity condition ensures nonexplosion. → The minimal Markov-renewal realization, killed at explosion, with hitting restricted to finite indexed entries.; reason: The Bernoulli-divergence argument on p. 21 fails for unbounded epsilon. The explicit completion preserves every finite path and excludes unspecified post-explosion resurrection; no nonexplosion premise is added. See DISPROOF.md.
--   - reading: (ii) and (iii) hold for all λ, ν. → (ii) and (iii) are required for λ = ν and for every pair with p_{λν} ≠ 0.; reason: The footnote on p. 19 leaves Ω_{λν} undefined when p_{λν} = 0; the Lean filler laws at such pairs do not affect any probability, so they are not constrained.
--   - encoding: Real time and the paper’s distribution-function notation. → Probability measures with explicit mass at infinity and real-time limits; lattice sampling alone uses natural indices.; reason: Preserve defective laws, infinite means and the exact asymptotic domain without total-function defaults.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 22, Theorem 6

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_SMProcess

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), Theorem 6, p. 22, all five premises and both conclusions.
Formalization Note: 'not periodic' is corrected to aperiodic return laws for both
processes (see Theorem 5 and DISPROOF.md). No coupling is required. Equality of
all pairwise means includes the unconditional diagonal and infinite values.
Conditions (ii)–(iii) are required only where Ω_λν is defined (λ = ν, or p_λν ≠ 0;
the footnote on p. 19 leaves Ω_λν undefined when p_λν = 0). Only
one selected-state unconditional mean need be finite. Regularity remains (4·4·1);
no nonexplosion is presumed from that condition. Minimal occupation is killed at
explosion rather than continued by an arbitrary resurrection. -/
theorem theorem_6 {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (M₁ : SMProcess Ω₁) (M₂ : SMProcess Ω₂)
    (hr₁ : M₁.S.Regular) (hr₂ : M₂.S.Regular)
    (z μ : ℕ) (haper₁ : Aperiodic (M₁.returnLaw μ))
    (haper₂ : Aperiodic (M₂.returnLaw μ))
    (hp : ∀ i j : ℕ, M₁.S.p i j = M₂.S.p i j)
    (hΩ : ∀ i j : ℕ, (i = j ∨ M₁.S.p i j ≠ 0) →
      M₁.S.waitLaw i j (Set.Iio ⊤) = M₂.S.waitLaw i j (Set.Iio ⊤))
    (hm : ∀ i j : ℕ, (i = j ∨ M₁.S.p i j ≠ 0) → M₁.S.m i j = M₂.S.m i j)
    (hfinite : M₁.S.m μ μ < ⊤ ∨ M₂.S.m μ μ < ⊤) :
    ∃ L : ℝ,
      Tendsto (fun t : ℝ => (M₁.P z (M₁.inState μ t)).toReal) atTop (𝓝 L) ∧
      Tendsto (fun t : ℝ => (M₂.P z (M₂.inState μ t)).toReal) atTop (𝓝 L) := by sorry

end SmithRegenerative.Moments.Supplement
