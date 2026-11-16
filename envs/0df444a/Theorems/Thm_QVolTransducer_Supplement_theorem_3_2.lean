-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_2
-- name    : QVolTransducer.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:35:39.799541+00:00
-- url     : https://prove2.me/theorems/478e9329-3e24-45c8-b2f1-cb6df119e4ee
-- title:
--   Theorem 3.2 — amplitude-amplification adversary solution
-- statement:
--   Let $\mathcal D$ be a set and, for every $x\in\mathcal D$, let $|\psi_x^0\rangle,|\psi_x^1\rangle\in\mathcal H$ with $\|\psi_x^0\|^2+\|\psi_x^1\|^2=1$ and $\|\psi_x^0\|,\|\psi_x^1\|>0$. Put
--
--   $$|\psi_x\rangle=|\psi_x^0\rangle|0\rangle+|\psi_x^1\rangle|1\rangle,\qquad |\bar\psi_x\rangle=\frac{\|\psi_x^1\|}{\|\psi_x^0\|}|\psi_x^0\rangle|0\rangle-\frac{\|\psi_x^0\|}{\|\psi_x^1\|}|\psi_x^1\rangle|1\rangle.$$
--
--   Suppose $\{|v_x^\pm\rangle,|\bar v_x^\pm\rangle\}_{x\in\mathcal D}$ is a feasible solution to the bidirectional adversary bound for $\{(|\psi_x\rangle,|\psi_x\rangle,O_x),(|\bar\psi_x\rangle,-|\bar\psi_x\rangle,O_x)\}_{x\in\mathcal D}$. Then there is a feasible solution $\{|w_x^\pm\rangle,|\bar w_x^\pm\rangle\}_{x\in\mathcal D}$ for
--
--   $$\Big\{\Big(|\psi_x\rangle,\ \frac{|\psi_x^1\rangle}{\|\psi_x^1\|}|1\rangle,\ O_x\Big),\ \Big(|\bar\psi_x\rangle,\ -\frac{|\psi_x^0\rangle}{\|\psi_x^0\|}|0\rangle,\ O_x\Big)\Big\}_{x\in\mathcal D}$$
--
--   with, for both signs,
--
--   $$\|w_x^\pm\|^2=\frac{(1+2\|\psi_x^1\|)\|v_x^\pm\|^2+\|\psi_x^0\|^2\|\bar v_x^\pm\|^2}{4\|\psi_x^1\|}\le\frac{\|v_x^\pm\|^2+\|\bar v_x^\pm\|^2}{4\|\psi_x^1\|}+\frac{\|v_x^\pm\|^2}2,$$
--   $$\|\bar w_x^\pm\|^2=\frac{(1+2\|\psi_x^1\|)\|\bar v_x^\pm\|^2+\|\psi_x^0\|^2\|v_x^\pm\|^2}{4\|\psi_x^1\|}\le\frac{\|v_x^\pm\|^2+\|\bar v_x^\pm\|^2}{4\|\psi_x^1\|}+\frac{\|\bar v_x^\pm\|^2}2.$$
--
--   This is exact amplitude amplification at the level of adversary-bound solutions: the cost grows like $1/\|\psi_x^1\|$, and no garbage is produced.
--
--   **Formalization Note** The two instances of each input are indexed by $\mathcal D\times\mathrm{Fin}\,2$ ($0$: the $|\psi_x\rangle$ instance, $1$: the $|\bar\psi_x\rangle$ instance), the sign by a Boolean. The new workspace is existentially quantified (any complex Hilbert space).
--
--   Differences from the source:
--   - encoding: two instances per input x → instances indexed by D × Fin 2 (0: ψ_x, 1: ψ̄_x), signs by a Boolean; reason: same problem
--   - encoding: the state space H, the oracle space, the workspace W → ℂ^S and ℂ^Q for finite types; W any complex Hilbert space; reason: Part I's state and oracle spaces are finite-dimensional; W is general as in Definition 2.2 (the proof needs L²(0,∞))
--   - reading: we can construct a feasible solution → there exist a complex Hilbert space W′ and a feasible solution in ℂ^Q ⊗ W′; reason: the construction (pp.18–19) uses the workspace (W ⊗ L²(0,∞))² ⊕ W, so the workspace is not the given one
--   - reading: ‖|ψ_0^x⟩‖ in the two norm formulas → ‖ψ_x^0‖; reason: typographical transposition of indices; the proof (p.19) uses a_x = ‖ψ_x^0‖
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_ampState
import Definitions.Def_QVolTransducer_Supplement_IsBiAdvSolution

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Amplitude-amplification adversary solution** (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Theorem 3.2, p.18 (PDF p.20)).

Let `D` be a set and, for every `x ∈ D`, `|ψ_x^0⟩, |ψ_x^1⟩ ∈ ℋ` with
`‖ψ_x^0‖² + ‖ψ_x^1‖² = 1` and `‖ψ_x^0‖, ‖ψ_x^1‖ > 0`; let `|ψ_x⟩ = |ψ_x^0⟩|0⟩ + |ψ_x^1⟩|1⟩` and
`|ψ̄_x⟩ = (‖ψ_x^1‖/‖ψ_x^0‖)|ψ_x^0⟩|0⟩ − (‖ψ_x^0‖/‖ψ_x^1‖)|ψ_x^1⟩|1⟩`. Given a feasible solution
`{|v_x^±⟩, |v̄_x^±⟩}_{x∈D}` to the bidirectional adversary bound for
`{(|ψ_x⟩, |ψ_x⟩, O_x), (|ψ̄_x⟩, −|ψ̄_x⟩, O_x)}_{x∈D}`, there is a feasible solution
`{|w_x^±⟩, |w̄_x^±⟩}_{x∈D}` (in some Hilbert-space workspace) for
`{(|ψ_x⟩, |ψ_x^1⟩|1⟩/‖ψ_x^1‖, O_x), (|ψ̄_x⟩, −|ψ_x^0⟩|0⟩/‖ψ_x^0‖, O_x)}_{x∈D}` with, for both signs,
`‖w_x^±‖² = ((1 + 2‖ψ_x^1‖)‖v_x^±‖² + ‖ψ_x^0‖²‖v̄_x^±‖²)/(4‖ψ_x^1‖)
  ≤ (‖v_x^±‖² + ‖v̄_x^±‖²)/(4‖ψ_x^1‖) + ‖v_x^±‖²/2` and
`‖w̄_x^±‖² = ((1 + 2‖ψ_x^1‖)‖v̄_x^±‖² + ‖ψ_x^0‖²‖v_x^±‖²)/(4‖ψ_x^1‖)
  ≤ (‖v_x^±‖² + ‖v̄_x^±‖²)/(4‖ψ_x^1‖) + ‖v̄_x^±‖²/2`.

**Formalization Note** The two instances of each input `x` are indexed by `D × Fin 2`: `(x, 0)` is
the `|ψ_x⟩` instance and `(x, 1)` the `|ψ̄_x⟩` instance, so `vp (x, 0) = |v_x^+⟩`,
`vp (x, 1) = |v̄_x^+⟩`, `vm (x, 0) = |v_x^−⟩`, `vm (x, 1) = |v̄_x^−⟩`, and likewise for `w`. The
state space `ℋ` is `ℂ^S` (finite `S`), the oracle space `ℂ^Q` (finite `Q`), and the workspaces are
arbitrary complex Hilbert spaces; `D` is arbitrary. The printed `‖|ψ_0^x⟩‖` is read `‖|ψ_x^0⟩‖`. The sign `±` is
`s : Bool` (`true` is `+`). -/
theorem theorem_3_2 {S Q W D : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (O : D → Matrix.unitaryGroup Q ℂ) (ψ0 ψ1 : D → EuclideanSpace ℂ S)
    (hnorm : ∀ x, ‖ψ0 x‖ ^ 2 + ‖ψ1 x‖ ^ 2 = 1) (h0 : ∀ x, 0 < ‖ψ0 x‖) (h1 : ∀ x, 0 < ‖ψ1 x‖)
    (vp vm : D × Fin 2 → TensorW Q W)
    (hv : IsBiAdvSolution
      (fun p : D × Fin 2 => ![ampState (ψ0 p.1) (ψ1 p.1), ampPerp (ψ0 p.1) (ψ1 p.1)] p.2)
      (fun p : D × Fin 2 => ![ampState (ψ0 p.1) (ψ1 p.1), -ampPerp (ψ0 p.1) (ψ1 p.1)] p.2)
      (fun p => (O p.1 : Matrix Q Q ℂ)) vp vm) :
    ∃ (W' : Type) (_ : NormedAddCommGroup W') (_ : InnerProductSpace ℂ W') (_ : CompleteSpace W')
      (wp wm : D × Fin 2 → TensorW Q W'),
      IsBiAdvSolution
        (fun p : D × Fin 2 => ![ampState (ψ0 p.1) (ψ1 p.1), ampPerp (ψ0 p.1) (ψ1 p.1)] p.2)
        (fun p : D × Fin 2 =>
          ![tensorVec ((((‖ψ1 p.1‖ : ℝ) : ℂ))⁻¹ • ψ1 p.1) (ket (1 : Fin 2)),
            -tensorVec ((((‖ψ0 p.1‖ : ℝ) : ℂ))⁻¹ • ψ0 p.1) (ket (0 : Fin 2))] p.2)
        (fun p => (O p.1 : Matrix Q Q ℂ)) wp wm ∧
      ∀ x, ∀ s : Bool,
        ‖(if s then wp else wm) (x, 0)‖ ^ 2 =
            ((1 + 2 * ‖ψ1 x‖) * ‖(if s then vp else vm) (x, 0)‖ ^ 2 +
              ‖ψ0 x‖ ^ 2 * ‖(if s then vp else vm) (x, 1)‖ ^ 2) / (4 * ‖ψ1 x‖) ∧
        ((1 + 2 * ‖ψ1 x‖) * ‖(if s then vp else vm) (x, 0)‖ ^ 2 +
              ‖ψ0 x‖ ^ 2 * ‖(if s then vp else vm) (x, 1)‖ ^ 2) / (4 * ‖ψ1 x‖) ≤
            (‖(if s then vp else vm) (x, 0)‖ ^ 2 + ‖(if s then vp else vm) (x, 1)‖ ^ 2) /
              (4 * ‖ψ1 x‖) + ‖(if s then vp else vm) (x, 0)‖ ^ 2 / 2 ∧
        ‖(if s then wp else wm) (x, 1)‖ ^ 2 =
            ((1 + 2 * ‖ψ1 x‖) * ‖(if s then vp else vm) (x, 1)‖ ^ 2 +
              ‖ψ0 x‖ ^ 2 * ‖(if s then vp else vm) (x, 0)‖ ^ 2) / (4 * ‖ψ1 x‖) ∧
        ((1 + 2 * ‖ψ1 x‖) * ‖(if s then vp else vm) (x, 1)‖ ^ 2 +
              ‖ψ0 x‖ ^ 2 * ‖(if s then vp else vm) (x, 0)‖ ^ 2) / (4 * ‖ψ1 x‖) ≤
            (‖(if s then vp else vm) (x, 0)‖ ^ 2 + ‖(if s then vp else vm) (x, 1)‖ ^ 2) /
              (4 * ‖ψ1 x‖) + ‖(if s then vp else vm) (x, 1)‖ ^ 2 / 2 := by sorry

end QVolTransducer.Supplement
