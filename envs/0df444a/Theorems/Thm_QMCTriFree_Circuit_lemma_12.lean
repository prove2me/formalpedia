-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_12
-- name    : QMCTriFree.Circuit.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:50.069552+00:00
-- url     : https://prove2.me/theorems/c3fa678d-4938-4c00-82f7-f226f6b54c61
-- title:
--   Lemma 12 — on a triangle-free graph, the expected energy of $h_{ij}$ after the random commuting circuit obeys the lower bound (11)
-- statement:
--   Let $(V,\{w_{ij}\})$ be a triangle-free weighted graph, $\bigotimes_k|v_k\rangle$ a product state with Bloch vectors $\vec v_k\in S^2$, and $\theta_{kl}=\theta_{lk}$ real angles. Choose the equatorial $P_k$ and the signs $\varepsilon_{kl}$ as in Algorithm 17 and apply $U=\prod_{kl}\exp(i\varepsilon_{kl}\theta_{kl}P_k\otimes P_l)$, the product over all edges. For an edge $(i,j)$ write $j\ne k\sim i$ for the neighbours $k$ of $i$ other than $j$. Then the energy on $h_{ij}$, averaged over the random $P_k$, satisfies
--   $$\langle h_{ij}\rangle\ \ge\ E_{ij}\Bigl(\tfrac12+\tfrac12\prod_{j\ne k\sim i}\cos2\theta_{ik}\cdot\prod_{i\ne l\sim j}\cos2\theta_{lj}+\tfrac1\pi\sin2\theta_{ij}\Bigl(\prod_{j\ne k\sim i}\cos2\theta_{ik}+\prod_{i\ne l\sim j}\cos2\theta_{lj}\Bigr)\Bigr),$$
--   with $E_{ij}=\tfrac12(1-\vec v_i\cdot\vec v_j)$.
--
--   The last term is the gain from rotating edge $(i,j)$ towards the singlet; the product term records the loss caused by the rotations of the neighbouring edges. This is the only place where triangle-freeness is used.
--
--   **Formalization Note** The angles are arbitrary symmetric reals (the paper's proof uses no range restriction). The expectation is over the Gaussian representation of the equator draws, for the product state held fixed.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 11, Lemma 12, eq. (11) (restated as Lemma 21, p. 23, proved pp. 24–26)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 11, Lemma 12 (eq. (11); restated as Lemma 21, p. 23): on a
triangle-free graph, for any product state of unit Bloch vectors and any symmetric angles, the
expected energy on the edge term `h_ij` of the random commuting circuit state, averaged over the
equatorial `P_k`, is at least
`E_ij(½ + ½ ∏_{j≠k∼i} cos 2θ_ik ∏_{i≠l∼j} cos 2θ_lj + (1/π) sin 2θ_ij (∏_{j≠k∼i} cos 2θ_ik +
∏_{i≠l∼j} cos 2θ_lj))`. -/
theorem lemma_12 {n : ℕ} (w : Fin n → Fin n → ℝ) (hw : IsWeightedGraph w)
    (htf : IsTriangleFree w) (θ : Fin n → Fin n → ℝ) (hθ : ∀ k l, θ k l = θ l k)
    (v : Fin n → Fin 3 → ℝ) (hv : ∀ k, v k ⬝ᵥ v k = 1)
    (i j : Fin n) (hij : i ≠ j) (hwij : w i j ≠ 0) :
    Eij v i j *
        (1 / 2 + 1 / 2 * (∏ k ∈ (nbrs w i).erase j, Real.cos (2 * θ i k)) *
            (∏ l ∈ (nbrs w j).erase i, Real.cos (2 * θ l j)) +
          1 / Real.pi * Real.sin (2 * θ i j) *
            ((∏ k ∈ (nbrs w i).erase j, Real.cos (2 * θ i k)) +
              ∏ l ∈ (nbrs w j).erase i, Real.cos (2 * θ l j))) ≤
      avgEdgeEnergy w θ v i j := by sorry

end QMCTriFree.Circuit
