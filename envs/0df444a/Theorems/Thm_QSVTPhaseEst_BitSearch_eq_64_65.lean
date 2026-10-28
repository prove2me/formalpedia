-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_eq_64_65
-- name    : QSVTPhaseEst.BitSearch.eq_64_65
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:28.680366+00:00
-- url     : https://prove2.me/theorems/cc76f0bf-e870-4a1f-8fdf-730b30a82ce0
-- title:
--   (64)–(65), p. 15 — A_j(θ) acts on |u⟩ with singular value σ^j = |cos(π(2^jφ − θ))| = |cos(π(0.φ_{j+1}φ_{j+2}… − θ))|
-- statement:
--   Let $U$ be an $N \times N$ unitary matrix and $u$ a vector with $Uu = e^{2\pi i\varphi}u$. For $j \in \mathbb N$ and $\theta \in \mathbb R$ put
--   $$A_j(\theta) = \tfrac12\bigl(I + e^{-2\pi i\theta}U^{2^j}\bigr), \qquad x = 2^j\varphi - \theta.$$
--   Then
--
--   1. $A_j(\theta)\,u = \cos(\pi x)\,e^{i\pi x}\,u$;
--   2. $A_j(\theta)^\dagger\bigl(e^{i\pi x}u\bigr) = \cos(\pi x)\,u$;
--   3. the singular value $\sigma^j = |\cos(\pi x)|$ of (64) can be re-expressed as in (65),
--   $$\sigma^j = \bigl|\cos\bigl(\pi(0.\varphi_{j+1}\varphi_{j+2}\ldots - \theta)\bigr)\bigr|,$$
--   where $0.\varphi_{j+1}\varphi_{j+2}\ldots$ is the fractional part of $2^j\varphi$.
--
--   Items 1 and 2 say that $|u\rangle$ is a right singular vector and $e^{i\pi x}|u\rangle$ (up to the sign of $\cos\pi x$) a left singular vector of $A_j(\theta)$ for the singular value $|\cos(\pi x)|$. This is what lets each iteration of phase estimation by QSVT read one binary digit of $\varphi$.
--
--   **Formalization Note** With singular value $|\cos\pi x|$ the left singular vector is $\operatorname{sign}(\cos\pi x)\,e^{i\pi x}|u\rangle$; the statement gives the two identities, which hold without the sign. The fractional part is `Int.fract`; the paper's intermediate identity $\exp(\pi i 2^j\varphi) = \exp(\pi i\,0.\varphi_{j+1}\ldots)$ holds only up to a sign $\pm1$, which the absolute value removes.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 15, (64) and (65)

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem eq_64_65 {N : Type} [Fintype N] [DecidableEq N] (U : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ) (u : N → ℂ) (φ θ : ℝ) (j : ℕ)
    (hUu : U.mulVec u = Complex.exp (2 * Real.pi * Complex.I * φ) • u) :
    let A : Matrix N N ℂ :=
      (1 / 2 : ℂ) • (1 + Complex.exp (-2 * Real.pi * Complex.I * θ) • U ^ (2 ^ j))
    let x : ℝ := (2 : ℝ) ^ j * φ - θ
    A.mulVec u = ((Real.cos (Real.pi * x) : ℂ) * Complex.exp (Real.pi * Complex.I * x)) • u ∧
    A.conjTranspose.mulVec (Complex.exp (Real.pi * Complex.I * x) • u) =
      (Real.cos (Real.pi * x) : ℂ) • u ∧
    sigma φ j θ = |Real.cos (Real.pi * (Int.fract ((2 : ℝ) ^ j * φ) - θ))| := by sorry

end QSVTPhaseEst.BitSearch
