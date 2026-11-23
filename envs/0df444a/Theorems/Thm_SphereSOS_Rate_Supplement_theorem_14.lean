-- Prove2me | Theorems.Thm_SphereSOS_Rate_Supplement_theorem_14
-- name    : SphereSOS.Rate.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:08:37.720798+00:00
-- url     : https://prove2.me/theorems/9acd1a30-0a1b-4093-8e25-fc933f12d511
-- title:
--   Theorem 14 (NOP09; companion theorem) — quadratic-rate mixing of DPS states into separable states
-- statement:
--   Let $d_A,d_B\ge1$, let $\ell\ge1$ be an integer, and let $\rho_{AB}$ be a trace-one state in the $\ell$-th DPS relaxation. Put $\rho_A=\operatorname{Tr}_B\rho_{AB}$ and let $I_B$ be the identity on $\mathbb C^{d_B}$. There is an absolute constant $C>0$ such that, for each $d_B$ and $\ell$, a mixing amount $t\in[0,1]$ can be chosen, uniformly in $d_A$ and the state, with
--
--   $$
--   t\le C\frac{d_B^2}{\ell^2},\qquad
--   (1-t)\rho_{AB}+t\rho_A\otimes\frac{I_B}{d_B}\in\operatorname{Sep}(d_A,d_B).
--   $$
--
--   This is the state mixing convergence theorem attributed to Navascués, Owari and Plenio on p. 13. It is a companion theorem, not used to prove the published goal. The mixture is required to have trace one as well as lie in the separable cone.
--
--   Differences from the source:
--
--   - encoding: positive subsystem dimensions and level ℓ → natural dimensions with 0 < dA and 0 < dB; ℓ = m + 1; reason: finite-dimensional quantum systems are nonzero and the hierarchy starts at level 1; this avoids zero division and truncated level subtraction
--   - encoding: ρ_A := Tr_B[ρ_AB] and membership in Sep(d) → ρA i j := ∑ b, ρ (i,b) (j,b); σ ∈ SEPcone dA dB and σ.trace = 1; reason: partial trace is constructed, and the published SEPcone is unnormalized, so trace one is stated explicitly; ρ.trace = 1 expresses the printed quantum-state normalization
--   - reading: t = O(d_B²/ℓ²) → there is an absolute C > 0; for each dB and level there exists t in [0,1] bounded by C*dB²/(m+1)², uniformly for all A dimensions and normalized DPS states; reason: uniform big-O quantifies the bound constant rather than a numerical formula; the paragraph after (27) identifies the fully mixed product as separable, so below a uniform linear asymptotic threshold t = 1 works after increasing C; no dimensions or levels are excluded
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 13, Theorem 14 (NOP09), (27); governing §4.1, pp. 10–12, (18), (20)–(23).

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.Rate.Supplement

open scoped Kronecker

/-- Fang–Fawzi, arXiv:1908.05155v1, Theorem 14 (NOP09), p. 13.
The mixing amount is uniform over the A dimension and all normalized DPS states.
The positive level is `ℓ = m + 1`. The big-O estimate is stated with an absolute
constant at all positive levels; below its asymptotic regime one may mix completely
(`t = 1`), as the paragraph after (27) notes that the product state is separable. -/
theorem theorem_14 :
    ∃ C : ℝ, 0 < C ∧
      ∀ dB m : ℕ, 0 < dB →
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
          t ≤ C * (dB : ℝ) ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 ∧
          ∀ (dA : ℕ), 0 < dA →
            ∀ ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ,
              ρ ∈ SphereSOS.DPS.DPScone dA dB m → ρ.trace = 1 →
              let ρA : Matrix (Fin dA) (Fin dA) ℂ :=
                fun i j => ∑ b : Fin dB, ρ (i, b) (j, b)
              let σ := ((1 - t : ℝ) : ℂ) • ρ +
                ((t / (dB : ℝ) : ℝ) : ℂ) •
                  (ρA ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))
              σ ∈ SphereSOS.DPS.SEPcone dA dB ∧ σ.trace = 1 := by sorry

end SphereSOS.Rate.Supplement
