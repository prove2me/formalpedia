-- Prove2me | Theorems.Thm_TeschlQM_Atomic_kato
-- name    : TeschlQM.Atomic.kato
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:00:39.489478+00:00
-- url     : https://prove2.me/theorems/6321fc77-d5bb-47c0-8cfa-043f0ffe6721
-- title:
--   Theorem 11.1 (Kato) — self-adjointness of N-body Hamiltonians on H²(ℝⁿ)
-- statement:
--   Let $N \ge 1$, $d \le 3$ and $n = Nd$. For $k$ in a finite index set, let $V_k \in L^\infty_\infty(\mathbb R^d) + L^2(\mathbb R^d)$ be real-valued, let $U_k$ be a unitary (orthogonal) transformation of $\mathbb R^n$, and let $y^{(k)} \in \mathbb R^d$ be the first $d$ coordinates of $U_k x$. Let $V_k(y^{(k)})$ be the multiplication operator in $L^2(\mathbb R^n)$ by $x \mapsto V_k(y^{(k)})$. Then every $V_k(y^{(k)})$ is $H_0$ bounded with $H_0$-bound $0$. In particular,
--   $$H = H_0 + \sum_k V_k(y^{(k)}), \qquad \mathfrak D(H) = H^2(\mathbb R^n),$$
--   is self-adjoint and $C_0^\infty(\mathbb R^n)$ is a core.
--
--   Applied to $V_{ne}(x_j)$ and $V_{ee}(x_j - x_k)$ (each a Coulomb potential of the first three coordinates after an orthogonal change of variables), this gives the self-adjointness of the atomic Hamiltonian $H^{(N)}$ on $H^2(\mathbb R^{3N})$, which the HVZ theorem presupposes.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin (N * d))`, $U_k$ is a linear isometry equivalence of it, and $y^{(k)}$ is `WithLp.toLp 2 (fun i : Fin d => U k x (Fin.castLE _ i))`. $H_0$ is `freeHamiltonian`, the sum is the `LinearPMap` sum (domain the intersection of the domains), and the conclusion `H.domain = (freeHamiltonian _).domain` is the claim $\mathfrak D(H) = H^2(\mathbb R^n)$. Self-adjointness is Mathlib's `IsSelfAdjoint`. "$C_0^\infty(\mathbb R^n)$ is a core" is stated as $C_0^\infty(\mathbb R^n) \subseteq \mathfrak D(H)$ and `(H.domRestrict C₀^∞).closure = H`. The hypothesis $N \ge 1$ is needed for "the first $d$ coordinates" of $\mathbb R^{Nd}$ to make sense.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 241, Theorem 11.1

import Mathlib
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_relativeBound
import Definitions.Def_TeschlQM_Atomic_MemLinftyInftyAddL2
import Definitions.Def_TeschlQM_Atomic_smoothCompactSupport

namespace TeschlQM.Atomic

open MeasureTheory

/-- Teschl, Theorem 11.1 (Kato), p. 241. Let `V_k ∈ L^∞_∞(ℝ^d) + L²(ℝ^d)`, `d ≤ 3`, be real-valued
(`k` ranging over a finite index set `K`) and let `V_k(y^{(k)})` be the multiplication operator in
`L²(ℝⁿ)`, `n = Nd`, obtained by letting `y^{(k)}` be the first `d` coordinates of `U_k x`, where
`U_k` is a unitary (orthogonal) transform of `ℝⁿ`. Then each `V_k(y^{(k)})` is `H₀` bounded with
`H₀`-bound `0`. In particular, `H = H₀ + ∑_k V_k(y^{(k)})` has domain `𝔇(H) = H²(ℝⁿ) = 𝔇(H₀)`, is
self-adjoint, and `C₀^∞(ℝⁿ)` is a core: `C₀^∞(ℝⁿ) ⊆ 𝔇(H)` and the closure of `H` restricted to
`C₀^∞(ℝⁿ)` is `H`. -/
theorem kato {N d : ℕ} (hN : 0 < N) (hd : d ≤ 3) {K : Type*} [Fintype K]
    (V : K → EuclideanSpace ℝ (Fin d) → ℝ) (hV : ∀ k, MemLinftyInftyAddL2 (V k))
    (U : K → EuclideanSpace ℝ (Fin (N * d)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (N * d))) :
    let Vy : K → EuclideanSpace ℝ (Fin (N * d)) → ℂ := fun k x =>
      ((V k (WithLp.toLp 2 (fun i : Fin d => U k x (Fin.castLE (Nat.le_mul_of_pos_left d hN) i)))
        : ℝ) : ℂ)
    let H := freeHamiltonian (Fin (N * d)) + ∑ k, mulOp volume (Vy k)
    (∀ k, TeschlQM.Shared.relativeBound (freeHamiltonian (Fin (N * d))) (mulOp volume (Vy k)) = 0) ∧
      H.domain = (freeHamiltonian (Fin (N * d))).domain ∧ IsSelfAdjoint H ∧
      smoothCompactSupport (Fin (N * d)) ≤ H.domain ∧
      (H.domRestrict (smoothCompactSupport (Fin (N * d)))).closure = H := by sorry

end TeschlQM.Atomic
