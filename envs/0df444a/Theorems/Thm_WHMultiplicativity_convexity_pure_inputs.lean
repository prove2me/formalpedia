-- Prove2me | Theorems.Thm_WHMultiplicativity_convexity_pure_inputs
-- name    : WHMultiplicativity.convexity_pure_inputs
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:40.706102+00:00
-- url     : https://prove2.me/theorems/c95c32f4-6c74-403b-bab7-f5a365826116
-- title:
--   §II, p.2: $\rho\mapsto\|S(\rho)\|_p$ is convex and takes its maximum on pure states
-- statement:
--   Let $d\ge 2$, let $S$ be the Werner–Holevo channel on $d\times d$ matrices, and let $1 \le p \le \infty$. Then:
--
--   1. the function $\rho \mapsto \|S(\rho)\|_p$ is convex on the set of $d\times d$ density matrices;
--   2. for every density matrix $\rho$ there is a unit vector $\varphi\in\mathbb C^d$ with
--
--   $$
--   \|S(\rho)\|_p \le \big\|S(|\varphi\rangle\langle\varphi|)\big\|_p .
--   $$
--
--   Part 2 is the form in which "takes its maximum on the extremal states" is used: to compute $\nu_p(S)$ it suffices to take pure input states.
--
--   Differences from the source:
--   - generalization: 1 < p < ∞ → every p : ℝ≥0∞ with 1 ≤ p (p = 1 and p = ∞ included); reason: the Schatten p-norm is a norm for every p ≥ 1; the page's range is contained
--   - reading: ρ ↦ ‖S(ρ)‖_p takes its maximum on the extremal states → every density matrix ρ has a unit vector φ with ‖S(ρ)‖_p ≤ ‖S(|φ⟩⟨φ|)‖_p; reason: the extremal density matrices are the pure states; a maximum over the compact set of states attained at a pure state is equivalent to this domination, which is what 'it suffices to take pure input states' uses
--   - encoding: ‖X‖_p = (tr|X|^p)^{1/p} for real p, and ‖·‖_∞ the operator norm → schattenNorm p X with p : ℝ≥0∞, a real p entering as ENNReal.ofReal p and ∞ as ⊤; reason: tr|X|^p = tr (XᴴX)^{p/2}; ⊤ gives the ℓ² operator norm; same values
--   - encoding: matrix transpose and conjugates with respect to some fixed basis → the standard basis of ℂ^d (index Fin d); reason: any fixed basis; the statement is the same up to a unitary change of basis
--   - encoding: d × d matrices with denominator d − 1 (d ≥ 2 implicit) → hypothesis 2 ≤ d; reason: excludes only d = 1, where the page's formula divides by zero
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, §II, p.2 (sentence before eq. (8))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_schattenNorm

open scoped ENNReal
open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, §II, p.2 (before eq. (8)): "Now ρ ↦ ‖S(ρ)‖_p is a
convex function, and hence takes its maximum on the extremal states. Therefore it suffices to take
pure input states". Both halves: (a) `ρ ↦ ‖S(ρ)‖_p` is convex on the density matrices; (b) for
every density matrix `ρ` there is a unit vector `φ` with `‖S(ρ)‖_p ≤ ‖S(|φ⟩⟨φ|)‖_p`.

**Formalization Note.** `S = wernerHolevo d`, `‖·‖_p = schattenNorm p` with `p : ℝ≥0∞`
(`⊤` the operator norm), `|φ⟩⟨φ| = pureState φ`. The paper's range is `1 < p < ∞`; the
statement covers every `1 ≤ p ≤ ∞`. "Takes its maximum on the extremal states" is stated in the
form the paper uses it: every output norm is dominated by the output norm of a pure input. -/
theorem convexity_pure_inputs (d : ℕ) (hd : 2 ≤ d) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ConvexOn ℝ {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensity ρ}
        (fun ρ => schattenNorm p (wernerHolevo d ρ)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ →
        ∃ φ : Fin d → ℂ, IsUnitVector φ ∧
          schattenNorm p (wernerHolevo d ρ) ≤ schattenNorm p (wernerHolevo d (pureState φ)) := by sorry

end WHMultiplicativity
