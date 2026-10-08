-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_unique_one_eigenvector
-- name    : QuantumWalkSearch.PhaseReflection.unique_one_eigenvector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:44.839984+00:00
-- url     : https://prove2.me/theorems/28e2d4e3-d44f-4e35-9cd5-ba991d5c0c97
-- title:
--   §3.2 — for ergodic reversible $P$, $|\pi\rangle$ is the unique $1$-eigenvector of $W(P)$ in $\mathcal A+\mathcal B$; other eigenvalues are $\Delta(P)$ away from $1$
-- statement:
--   Let $P$ be an ergodic (irreducible and aperiodic) and reversible Markov chain on a finite set $X$ with stationary distribution $\pi$, $W(P)$ its quantum walk, $|\pi\rangle=\sum_x\sqrt{\pi_x}|x\rangle|p_x\rangle$ and $\Delta(P)$ the phase gap. Then:
--
--   1. $|\pi\rangle\in\mathcal A\cap\mathcal B$ and $W(P)|\pi\rangle=|\pi\rangle$;
--   2. every $v\in\mathcal A+\mathcal B$ with $W(P)v=v$ is a scalar multiple of $|\pi\rangle$;
--   3. every other eigenvalue $\mu\neq1$ of $W(P)$ with an eigenvector in $\mathcal A+\mathcal B$ is at angular distance at least $\Delta(P)$ from $1$:
--   $$|1-\mu|\ \ge\ \big|1-e^{i\Delta(P)}\big| .$$
--
--   This is the observation of §3.2 that makes phase estimation useful: inside $\mathcal A+\mathcal B$, the eigenvalue $1$ singles out $|\pi\rangle$, and the remaining eigenvalues are bounded away from $1$ by the phase gap.
--
--   **Formalization Note** "Ergodic" is `Matrix.IsPrimitive` (some power of $P$ is entrywise positive), equivalent to irreducible and aperiodic for a finite chain. Reversibility is the standing assumption of §3.2 (p. 8); without it the statement can fail. "Bounded away from 1" is made quantitative with the paper's own remark after the definition of $\Delta(P)$ (p. 7: "the angular distance of 1 from any other eigenvalue is at least $\Delta(P)$"); since $0<\Delta(P)\le\pi$, the inequality on $|1-\mu|$ is equivalent to that angular distance bound. With the convention $\Delta(P)=\pi$ (no singular value in $(0,1)$) item 3 says the only other eigenvalue is $-1$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, §3.2, p. 9 (unnumbered: "|π⟩ is the unique eigenvector of the unitary operator W(P) in A + B with eigenvalue 1, and the remaining eigenvalues in A + B are bounded away from 1"); standing assumption p. 8; angular distance remark p. 7

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_Walk

namespace QuantumWalkSearch.PhaseReflection

/-- §3.2, p. 9: for an ergodic (irreducible and aperiodic, i.e. primitive) reversible chain, `|π⟩`
is the unique (up to scalars) eigenvector of `W(P)` in `A + B` with eigenvalue `1`, and every other
eigenvalue of `W(P)` on `A + B` is at angular distance at least `Δ(P)` from `1` (p. 7), i.e.
`|1 − μ| ≥ |1 − e^{iΔ(P)}|`. -/
theorem unique_one_eigenvector {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (πd : X → ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (herg : P.IsPrimitive)
    (hπ : IsStationaryDist P πd) (hrev : IsReversible P πd) :
    piState P πd ∈ spaceA P ⊓ spaceB P πd ∧
    walk P πd (piState P πd) = piState P πd ∧
    (∀ v ∈ spaceA P ⊔ spaceB P πd, walk P πd v = v → ∃ c : ℂ, v = c • piState P πd) ∧
    (∀ (μ : ℂ), ∀ v ∈ spaceA P ⊔ spaceB P πd, v ≠ 0 → walk P πd v = μ • v → μ ≠ 1 →
      ‖1 - Complex.exp ((phaseGap P πd : ℂ) * Complex.I)‖ ≤ ‖1 - μ‖) := by sorry

end QuantumWalkSearch.PhaseReflection
