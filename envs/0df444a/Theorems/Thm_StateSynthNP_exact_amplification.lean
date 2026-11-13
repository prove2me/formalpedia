-- Prove2me | Theorems.Thm_StateSynthNP_exact_amplification
-- name    : StateSynthNP.exact_amplification
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:48:49.436287+00:00
-- url     : https://prove2.me/theorems/a95ea9a1-9075-450a-a96a-7203182ee2af
-- title:
--   Exact amplitude amplification at success probability $\tfrac12$ [BHMT00]
-- statement:
--   Let $U$ be a unitary matrix, $v_0$ a unit vector and $\Pi$ an orthogonal projector (Hermitian and idempotent) with
--
--   $$
--   \|\Pi\,U v_0\|^2=\tfrac12 .
--   $$
--
--   Then one generalized amplitude-amplification iterate with phases $\pi/2$, $Q=-U\,S_{v_0}(\pi/2)\,U^{\dagger}\,S_{\Pi}(\pi/2)$, satisfies
--
--   $$
--   Q\,U v_0=(1-i)\,\Pi\,U v_0 ,
--   $$
--
--   so $Q\,Uv_0$ lies in the range of $\Pi$ and $\|\Pi\,Q\,Uv_0\|^2=1$.
--
--   Applied to the ideal state $|\psi''\rangle$, whose good branch has probability exactly $\tfrac12$, it outputs the target state exactly, up to the global phase $(1-i)/\sqrt2$. With the standard Grover phases $\pi$ the success probability would stay $\tfrac12$.
--
--   Differences from the source:
--
--   - reading: boost the probability of the good branch from ≈ 1/2 to ≈ 1 by exact amplitude amplification [BHMT00] → at probability exactly 1/2, one iterate with phases π/2 maps U v₀ to (1 − i) Π U v₀; reason: the ideal state has probability exactly 1/2 and becomes exactly |ψ⟩ (p.5); the approximate case is the error propagation milestone; the paper does not name the phases, and π/2 is the choice that makes one iterate exact
--   - encoding: unitaries and projectors on the state space → complex square matrices indexed by a finite type: U in the unitary group, Π Hermitian with Π² = Π, v₀ of squared norm 1; reason: finite-dimensional state space; same objects
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Theorem 2.1, p.4 ("we just run an exact amplitude amplification algorithm [BHMT00] to boost the probability of the |1⟩ branch from ≈ 1/2 to ≈ 1"); proof of Lemma 2.2, p.5 ("After constant rounds of amplitude amplification, note that |ψ''⟩ becomes exactly |ψ⟩")

import Mathlib
import Definitions.Def_StateSynthNP_ampIterate

set_option autoImplicit false

namespace StateSynthNP

/-- **Exact amplitude amplification at success probability 1/2** ([BHMT00]).

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Theorem 2.1, p.4: "Notice that the probability on the good branch is
≈ 1/2 … So, we just run an exact amplitude amplification algorithm [BHMT00] to boost the probability
of the |1⟩ branch from ≈ 1/2 to ≈ 1", and proof of Lemma 2.2, p.5: "After constant rounds of
amplitude amplification, note that |ψ''⟩ becomes exactly |ψ⟩".

Statement: let `U` be a unitary matrix, `v₀` a unit vector and `Π` an orthogonal projector with
`‖Π U v₀‖² = 1/2`. Then one generalized iterate `Q = − U S_{v₀}(π/2) U† S_Π(π/2)` maps `U v₀` to
`(1 − i) Π U v₀`; in particular `Q U v₀` lies in the range of `Π` and `‖Π Q U v₀‖² = 1`.

**Formalization Note.** The phases are `π/2`; with the standard phases `π` the success probability
stays `1/2`. -/
theorem exact_amplification {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (v₀ : ι → ℂ) (hv₀ : ∑ i, Complex.normSq (v₀ i) = 1)
    (P : Matrix ι ι ℂ) (hPh : P.IsHermitian) (hPi : P * P = P)
    (hhalf : ∑ i, Complex.normSq ((P.mulVec (U.mulVec v₀)) i) = 1 / 2) :
    (ampIterate U v₀ P (Real.pi / 2)).mulVec (U.mulVec v₀) = (1 - Complex.I) • P.mulVec (U.mulVec v₀) ∧
    ∑ i, Complex.normSq ((P.mulVec ((ampIterate U v₀ P (Real.pi / 2)).mulVec (U.mulVec v₀))) i) = 1 := by sorry

end StateSynthNP
