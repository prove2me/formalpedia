-- Prove2me | Theorems.Thm_QPVEntanglement_Supplement_theorem_8
-- name    : QPVEntanglement.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:21:55.383206+00:00
-- url     : https://prove2.me/theorems/9df2efcc-a31f-4bbe-bcc1-aa8281e38ea6
-- title:
--   Theorem 8 — mobile-verifier security in every dimension $d\ge2$ against coalitions of $\lfloor m/\lceil\log_2^2\lambda\rceil\rfloor R_H(2\kappa(s-2.5)-1)$ qubits
-- statement:
--   This item is stated in the **operator-requested pinned-down model** of the paper's adversary model (§4, pp.28–29). The paper defines its coalitions only operationally, so the mission fixes a precise model (choices P1–P14 of the mission description, here carried from $\mathbb R$ to $\mathbb R^d$) and states the paper's result in it at full strength.
--
--   There is a universal constant $\kappa>0.08$ with the following property. Let $d\ge2$, and let $m,R_H,s:\mathbb N\to\mathbb N$ be polynomially bounded functions of the security parameter $\lambda$ with $s\ge9$, $R_H\ge1$ and $m=\omega(\log_2^2\lambda)$ (the assumptions of Theorem 7). Put
--
--   $$B(\lambda)=\Big\lfloor\frac{m}{\lceil\log_2^2(\lambda)\rceil}\Big\rfloor R_H\big(2\kappa(s-2.5)-1\big).$$
--
--   The $d$-dimensional mobile-verifier version of the protocol of Figure 3 (Definition 4) has $B(\lambda)$-qubit mobile-verifier security. Fix any $d$-dimensional geometry, that is, a claimed location together with a verifier pair placed on a line through it. Then for every family, indexed by $\lambda$, of schedules and coalitions in $\mathbb R^d$ with no station at the claimed location and quantum-register size at most $B(\lambda)$, there is a negligible function $\mathrm{negl}$ with
--
--   $$\Pr[\text{the coalition of index }\lambda\text{ is accepted}]\le\mathrm{negl}(\lambda)\qquad\text{for every }\lambda .$$
--
--   Adversaries may sit anywhere in $\mathbb R^d$, off the verifier line included, and the security bound is the same as in one dimension.
--
--   Differences from the source:
--   - reading: finite d-dimensional adversarial coalition (§4 Adversary Model, clauses 1–6, pp.28–29; Definition 2, p.28) → `CoalitionD GD S` with `acceptProb` and `size`: the mission's pinned model P5–P11 with positions in ℝ^d and Euclidean travel times; reason: operator-requested pinned-down model (OPERATOR_NOTE 2026-11-11), carried to ℝ^d without changing any other rule
--   - generalization: Definition 4: claimed location z the midpoint, verifiers at z ± Ru → every GeometryD: any admissible one-dimensional geometry placed along a line o + r·u (‖u‖ = 1); reason: the midpoint placement is the case v₀ = x − R, v₁ = x + R; every placement Relocate(x) can produce is covered
--   - generalization: the directed slot instruction travels along the verifier axis (p.48) → visible at every point p of ℝ^d at time emit + ‖p − ι(v_b)‖₂; reason: more information for the coalition; the proof's map F_ε does not increase distances to the verifiers (p.47), so the mapped one-dimensional station still sees the instruction in time
--   - encoding: verifier inputs travel along the fixed path from V₀ through the claimed location to V₁ (condition 1, p.46) → a carrier can be absorbed only by a station at ι(r) with r on the verifier segment, exactly when it passes; reason: an off-axis station is never on the carrier's path (p.48)
--   - generalization: the coalition and the protocol's timing for each λ, with fixed locations → families (S λ, C λ) whose schedule, station number and positions may vary with λ; the geometry fixed; reason: more coalition families; the fixed-location case is a special case (as in the base goal)
--   - reading: m, R_H, s polynomial functions of λ; m = ω(log₂²λ) → published `PolyBounded`; m(λ)/log₂²λ → ∞ (`OmegaLogSq`); reason: as in the base goal: the weakest reading of 'polynomial' gives the strongest theorem
--   - encoding: κ > 0.08 the universal constant from Theorem 7 → ∃ κ > 0.08 quantified before d and every parameter; reason: Theorem 7 asserts only the existence of such a κ (the published goal states ∃ κ); the proofs use κ = 0.09 (p.45) for both
--   - encoding: In particular, it has Ω(smR_H/log²λ)-qubit mobile-verifier security → omitted; reason: a consequence of (41) (B(λ) ≥ c·smR_H/log²λ eventually), not a separate claim; as the published goal does for the parenthesis of (23)
--   - encoding: negligible function → published `Negligible` in an existential; reason: as in the base goal
--   - encoding: labels, rounds and slots 1-based → 0-based; reason: index shift
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 8, eq. (41), p.46; Definition 2, p.28; Definition 4, p.29; proof pp.47–49

import Mathlib
import Definitions.Def_QPVEntanglement_Supplement_CoalitionD_size
import Definitions.Def_QPVEntanglement_securityBound
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false

namespace QPVEntanglement.Supplement

open QPVEntanglement
open PPADSIS.SubexpSIS (Negligible PolyBounded)

/-- **Theorem 8 (Mobile-Verifier Security of the Protocol)**, p.46, stated in the
operator-requested pinned-down model of §4 (the published model of the mission, carried from `ℝ`
to `ℝ^d` through Definition 4). Behera–Goyal, *Breaking the Bounded Entanglement Barrier for
Quantum Position Verification*, arXiv:2609.39234 (sha256 bdf2928d…), Theorem 8, eq. (41), p.46;
Definition 2 (mobile-verifier security), p.28; Definition 4, p.29; proof pp.47–49.

There is a universal constant `κ > 0.08` such that for every dimension `d ≥ 2` and all parameter
functions `m, R_H, s` of `λ` satisfying the assumptions of Theorem 7 (polynomially bounded,
`s ≥ 9`, `R_H ≥ 1`, `m = ω(log₂² λ)`), the `d`-dimensional mobile-verifier version of the protocol
of Figure 3 has `B(λ) = ⌊m/⌈log₂²λ⌉⌋ · R_H · (2κ(s − 2.5) − 1)`-qubit mobile-verifier security:
for every `d`-dimensional geometry (claimed location and relocated verifier pair) and every
family of schedules and `d`-dimensional coalitions with no station at the claimed location and
size at most `B(λ)`, the acceptance probability is bounded by a negligible function of `λ`.

**Formalization Note.** `κ` is quantified before `d` and every parameter (Theorem 7 asserts only
`∃ κ > 0.08`; its proof takes `κ = 0.09`, p.45). The geometry is fixed; the schedule, the
coalition, its number of stations and their positions may vary with `λ`. The sentence "In
particular, it has `Ω(s m R_H / log² λ)`-qubit mobile-verifier security" is a consequence of (41)
and is not stated separately (as for the parenthesis of (23) in the published Theorem 7).
`Negligible`, `PolyBounded` are the published `PPADSIS.SubexpSIS` notions. -/
theorem theorem_8 :
    ∃ κ : ℝ, 0.08 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ m RH s : ℕ → ℕ, PolyBounded m → PolyBounded RH → PolyBounded s →
          (∀ lam, 9 ≤ s lam) → (∀ lam, 1 ≤ RH lam) → OmegaLogSq m →
          ∀ (GD : GeometryD d) (S : (lam : ℕ) → Schedule GD.G (m lam) (RH lam) (s lam))
            (C : (lam : ℕ) → CoalitionD GD (S lam)),
            (∀ lam a, (C lam).pos a ≠ GD.claimed) →
            (∀ lam, ((C lam).size : ℝ) ≤ securityBound κ m RH s lam) →
            ∃ negl : ℕ → ℝ, Negligible negl ∧ ∀ lam, (C lam).acceptProb ≤ negl lam := by sorry

end QPVEntanglement.Supplement
