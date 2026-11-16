-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_3_3
-- name    : QVolTransducer.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:36:15.933748+00:00
-- url     : https://prove2.me/theorems/e1840f44-3ef1-4c3d-babd-03d6f42667f6
-- title:
--   Theorem 3.3 — reflection through the amplified state
-- statement:
--   Let $\mathcal D$ be a set and, for $x\in\mathcal D$, let $|\psi_x^0\rangle,|\psi_x^1\rangle\in\mathcal H$ with $\|\psi_x^0\|^2+\|\psi_x^1\|^2=1$, $\|\psi_x^0\|,\|\psi_x^1\|>0$; let $|\psi_x\rangle$ and $|\bar\psi_x\rangle$ be as in Theorem 3.2, $|\tilde\psi_x\rangle:=|\tilde\psi_x^0\rangle|0\rangle$ and $|\hat\psi_x\rangle:=|\hat\psi_x^1\rangle|1\rangle$ with $\langle\hat\psi_x^1|\psi_x^1\rangle=0$, and $\varepsilon_x:=\|\psi_x^1\|$. Given a feasible solution $\{|v_x^\pm\rangle,|\bar v_x^\pm\rangle,|\tilde v_x^\pm\rangle,|\hat v_x^\pm\rangle\}_{x\in\mathcal D}$ to the bidirectional adversary bound for
--
--   $$P:=\{(|\psi_x\rangle,|\psi_x\rangle,O_x),(|\bar\psi_x\rangle,-|\bar\psi_x\rangle,O_x),(|\tilde\psi_x\rangle,-|\tilde\psi_x\rangle,O_x),(|\hat\psi_x\rangle,-|\hat\psi_x\rangle,O_x)\}_{x\in\mathcal D},$$
--
--   there is a feasible solution $\{|(w_x^0)^\pm\rangle,|(w_x^1)^\pm\rangle,|\tilde w_x^\pm\rangle,|\hat w_x^\pm\rangle\}_{x\in\mathcal D}$ for
--
--   $$P':=\Big\{\Big(\tfrac{|\psi_x^0\rangle|0\rangle}{\sqrt{1-\varepsilon_x^2}},-\tfrac{|\psi_x^0\rangle|0\rangle}{\sqrt{1-\varepsilon_x^2}},O_x\Big),\Big(\tfrac{|\psi_x^1\rangle|1\rangle}{\varepsilon_x},\tfrac{|\psi_x^1\rangle|1\rangle}{\varepsilon_x},O_x\Big),(|\tilde\psi_x\rangle,-|\tilde\psi_x\rangle,O_x),(|\hat\psi_x\rangle,-|\hat\psi_x\rangle,O_x)\Big\}_{x\in\mathcal D}$$
--
--   with
--
--   $$\|(w_x^0)^\pm\|^2=0,\qquad\|(w_x^1)^\pm\|^2=\frac{\|v_x^\pm\|^2}{\varepsilon_x^2},\qquad\|\tilde w_x^\pm\|^2=0,\qquad\|\hat w_x^\pm\|^2=\|\hat v_x^\pm\|^2.$$
--
--   It yields a reflection through the amplified state $|\psi_x^1\rangle/\|\psi_x^1\|$ without running the amplification circuit backwards.
--
--   **Formalization Note** The four instances are indexed by $\mathcal D\times\mathrm{Fin}\,4$ in the printed order. The new solution lies in the same workspace $\mathcal W$; $|\tilde\psi_x^0\rangle$ is arbitrary.
--
--   Differences from the source:
--   - encoding: four instances per input x → instances indexed by D × Fin 4 in the printed order, signs by a Boolean; reason: same problems P and P′
--   - encoding: the state space H, the oracle space, the workspace W → ℂ^S and ℂ^Q for finite types; W any complex Hilbert space; reason: Part I's state and oracle spaces are finite-dimensional; W is general as in Definition 2.2
--   - generalization: we can construct a feasible solution → a feasible solution in the same workspace W; reason: the proof's solution (p.20) uses the vectors v^±/ε_x, v̂^± and 0, which lie in W; a solution in W is in particular a solution
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 3.3, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_ampState
import Definitions.Def_QVolTransducer_Supplement_IsBiAdvSolution

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Reflection through the amplified state** (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Theorem 3.3, p.20 (PDF p.22)).

Let `D` be a set and, for every `x ∈ D`, `|ψ_x^0⟩, |ψ_x^1⟩ ∈ ℋ` with
`‖ψ_x^0‖² + ‖ψ_x^1‖² = 1` and `‖ψ_x^0‖, ‖ψ_x^1‖ > 0`; let `|ψ_x⟩ = |ψ_x^0⟩|0⟩ + |ψ_x^1⟩|1⟩`,
`|ψ̄_x⟩ = (‖ψ_x^1‖/‖ψ_x^0‖)|ψ_x^0⟩|0⟩ − (‖ψ_x^0‖/‖ψ_x^1‖)|ψ_x^1⟩|1⟩`, `|ψ̃_x⟩ := |ψ̃_x^0⟩|0⟩` and
`|ψ̂_x⟩ := |ψ̂_x^1⟩|1⟩` with `⟨ψ̂_x^1|ψ_x^1⟩ = 0`, and `ε_x := ‖ψ_x^1‖`. Given a feasible solution
`{|v_x^±⟩, |v̄_x^±⟩, |ṽ_x^±⟩, |v̂_x^±⟩}_{x∈D}` to the bidirectional adversary bound for
`P := {(|ψ_x⟩, |ψ_x⟩, O_x), (|ψ̄_x⟩, −|ψ̄_x⟩, O_x), (|ψ̃_x⟩, −|ψ̃_x⟩, O_x), (|ψ̂_x⟩, −|ψ̂_x⟩, O_x)}`,
there is a feasible solution `{|(w_x^0)^±⟩, |(w_x^1)^±⟩, |w̃_x^±⟩, |ŵ_x^±⟩}_{x∈D}` for
`P′ := {(|ψ_x^0⟩|0⟩/√(1 − ε_x²), −|ψ_x^0⟩|0⟩/√(1 − ε_x²), O_x), (|ψ_x^1⟩|1⟩/ε_x, |ψ_x^1⟩|1⟩/ε_x, O_x),
(|ψ̃_x⟩, −|ψ̃_x⟩, O_x), (|ψ̂_x⟩, −|ψ̂_x⟩, O_x)}` with `‖(w_x^0)^±‖² = 0`,
`‖(w_x^1)^±‖² = ‖v_x^±‖²/ε_x²`, `‖w̃_x^±‖² = 0` and `‖ŵ_x^±‖² = ‖v̂_x^±‖²`.

**Formalization Note** The four instances of each input `x` are indexed by `D × Fin 4` in the
printed order (`0`: `ψ`, `1`: `ψ̄`, `2`: `ψ̃`, `3`: `ψ̂` for `P`; `0`: `ψ^0`, `1`: `ψ^1`, `2`: `ψ̃`,
`3`: `ψ̂` for `P′`), the vectors `vp (x, i)`, `vm (x, i)` being the `+` and `−` vectors of
instance `i`. The constructed solution lies in the same workspace `𝒲` (the proof sets
`(w_x^1)^± := |v_x^±⟩/ε_x`, `ŵ_x^± := |v̂_x^±⟩` and the others `0`); this is stronger than "some
workspace". State space `ℂ^S`, oracle space `ℂ^Q` (finite `S`, `Q`), `𝒲` any complex Hilbert space,
`D` arbitrary; `|ψ̃_x^0⟩` is arbitrary. -/
theorem theorem_3_3 {S Q W D : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (O : D → Matrix.unitaryGroup Q ℂ) (ψ0 ψ1 ψt0 ψh1 : D → EuclideanSpace ℂ S)
    (hnorm : ∀ x, ‖ψ0 x‖ ^ 2 + ‖ψ1 x‖ ^ 2 = 1) (h0 : ∀ x, 0 < ‖ψ0 x‖) (h1 : ∀ x, 0 < ‖ψ1 x‖)
    (hperp : ∀ x, inner ℂ (ψh1 x) (ψ1 x) = 0)
    (vp vm : D × Fin 4 → TensorW Q W)
    (hv : IsBiAdvSolution
      (fun p : D × Fin 4 => ![ampState (ψ0 p.1) (ψ1 p.1), ampPerp (ψ0 p.1) (ψ1 p.1),
        tensorVec (ψt0 p.1) (ket (0 : Fin 2)), tensorVec (ψh1 p.1) (ket (1 : Fin 2))] p.2)
      (fun p : D × Fin 4 => ![ampState (ψ0 p.1) (ψ1 p.1), -ampPerp (ψ0 p.1) (ψ1 p.1),
        -tensorVec (ψt0 p.1) (ket (0 : Fin 2)), -tensorVec (ψh1 p.1) (ket (1 : Fin 2))] p.2)
      (fun p => (O p.1 : Matrix Q Q ℂ)) vp vm) :
    ∃ wp wm : D × Fin 4 → TensorW Q W,
      IsBiAdvSolution
        (fun p : D × Fin 4 =>
          ![(((Real.sqrt (1 - ‖ψ1 p.1‖ ^ 2) : ℝ) : ℂ))⁻¹ • tensorVec (ψ0 p.1) (ket (0 : Fin 2)),
            (((‖ψ1 p.1‖ : ℝ) : ℂ))⁻¹ • tensorVec (ψ1 p.1) (ket (1 : Fin 2)),
            tensorVec (ψt0 p.1) (ket (0 : Fin 2)), tensorVec (ψh1 p.1) (ket (1 : Fin 2))] p.2)
        (fun p : D × Fin 4 =>
          ![-((((Real.sqrt (1 - ‖ψ1 p.1‖ ^ 2) : ℝ) : ℂ))⁻¹ •
                tensorVec (ψ0 p.1) (ket (0 : Fin 2))),
            (((‖ψ1 p.1‖ : ℝ) : ℂ))⁻¹ • tensorVec (ψ1 p.1) (ket (1 : Fin 2)),
            -tensorVec (ψt0 p.1) (ket (0 : Fin 2)), -tensorVec (ψh1 p.1) (ket (1 : Fin 2))] p.2)
        (fun p => (O p.1 : Matrix Q Q ℂ)) wp wm ∧
      ∀ x, ∀ s : Bool,
        ‖(if s then wp else wm) (x, 0)‖ ^ 2 = 0 ∧
        ‖(if s then wp else wm) (x, 1)‖ ^ 2 = ‖(if s then vp else vm) (x, 0)‖ ^ 2 / ‖ψ1 x‖ ^ 2 ∧
        ‖(if s then wp else wm) (x, 2)‖ ^ 2 = 0 ∧
        ‖(if s then wp else wm) (x, 3)‖ ^ 2 = ‖(if s then vp else vm) (x, 3)‖ ^ 2 := by sorry

end QVolTransducer.Supplement
