-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_fluid_limit_existence
-- name    : ProcessingNetworks.PacketNetworks.fluid_limit_existence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:52:54.052044+00:00
-- url     : https://prove2.me/theorems/22975e6c-85e7-447d-9b01-0dd839ebef26
-- title:
--   Theorem 12.13 — existence of discrete-time fluid limits satisfying the fluid equations (milestone)
-- statement:
--   **Theorem 12.13.** Fix $\omega\in\Omega_1$ and an unbounded $G\subset\mathbb Z^I_+$. There is
--   a sequence $\{z_\ell\}\subset G$ and functions $\hat D,\hat T,\hat Z$ such that the
--   fluid-scaled raw processes converge to them u.o.c. (12.30), and every such limit satisfies
--   (12.31)–(12.36).
--
--   This is Chapter 12's analog of Theorem 6.5 (mission III), adapted to the discrete-time,
--   slotted model.
--
--   **Formalization note.** $\omega\in\Omega_1$ is the hypothesis `SLLNHoldsAt P lam ω` (the SLLN
--   (12.29) holds at $\omega$). The policy is admissible with values in $S$, Section 12.3's standing
--   assumption, which is what gives (12.33) $\hat Z\ge 0$ and (12.35) $\sum_{s\in S}\hat T_s(t)=t$.
--   "Every such limit" is quantified as the book states it: every u.o.c. limit along a sequence
--   from $G$ with $|z_\ell|\to\infty$ at this $\omega$ satisfies the fluid equations.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 236-237, Theorem 12.13, Eqs. (12.30)-(12.37)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

open Filter

/-- Theorem 12.13, Dai & Harrison p. 236 (PDF p. 252). Fix an admissible Markovian control policy
`f` (Section 12.3's standing assumption, with values in the schedule set `S`), a sample point
`ω ∈ Ω₁` (one at which the SLLN (12.29) holds for the arrival rate vector `λ`) and an unbounded set
`G ⊂ Z^I_+` (`hG`: `{|z| : z ∈ G}` is unbounded). There is a sequence `{zₗ} ⊂ G` with `|zₗ| → ∞` and
functions `D̂,T̂,Ẑ` such that the fluid-scaled raw processes converge to them u.o.c. (12.30), and
every such limit satisfies the fluid equations (12.31)-(12.36). -/
theorem fluid_limit_existence
    {I J : ℕ} {Ω : Type*} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (P : PacketPrimitives I J Ω) (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (lam : Fin I → ℝ) (ω : Ω) (hω : SLLNHoldsAt P lam ω)
    (G : Set (Fin I → ℕ)) (hG : ¬ BddAbove (sizeN '' G)) :
    (∃ zseq : ℕ → Fin I → ℕ, (∀ n, zseq n ∈ G) ∧ Tendsto (fun n => sizeN (zseq n)) atTop atTop ∧
      ∃ (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
        FluidScaledConverge dat P S ω zseq Dh Th Zh) ∧
    ∀ (zseq : ℕ → Fin I → ℕ) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
      (Zh : ℝ → Fin I → ℝ), (∀ n, zseq n ∈ G) → Tendsto (fun n => sizeN (zseq n)) atTop atTop →
      FluidScaledConverge dat P S ω zseq Dh Th Zh →
      SatisfiesPacketFluidEquations dat S lam Dh Th Zh := by sorry

end ProcessingNetworks.PacketNetworks
