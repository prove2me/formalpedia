-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_theorem_19
-- name    : QMCTriFree.Circuit.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:45.971404+00:00
-- url     : https://prove2.me/theorems/3a797eb9-2731-4fcb-9659-311789fffc35
-- title:
--   Theorems 3 and 19 — on triangle-free graphs Algorithm 17 has expected energy $E$ with $0.582\cdot\|H\|\le E\le\|H\|$
-- statement:
--   Let $(V,\{w_{ij}\})$ be a triangle-free weighted graph with nonnegative symmetric weights and total weight $\sum_{i<j}w_{ij}=1$, and let $H$ be its Quantum Max-Cut Hamiltonian. Let $M$ be any solution of $\mathrm{Lasserre}_2(H)$, $W$ any Gram factorisation of its $\mathcal P^{(1)}_n$ block, and $\beta\in[0,1]$ any parameter with
--   $$F(\beta;x)\ \ge\ 0.582\,(1+x)\qquad\text{for all }x\in[-1,1]$$
--   (the algorithm's choice $\beta^*\approx0.390$ is such a parameter). Run Algorithm 17: GP rounding of $M$ to Bloch vectors $\vec v_k$, angles $\theta_{ij}=\tfrac12\arcsin\beta x_{ij}$ for $x_{ij}\ge0$ and $0$ otherwise, random equatorial $P_k$, signs $\varepsilon_{ij}$ by rule (10), and the commuting circuit $\prod_{ij}\exp(i\varepsilon_{ij}\theta_{ij}P_i\otimes P_j)$ applied to $\bigotimes_k|v_k\rangle$. Its expected energy $E$ satisfies
--   $$0.582\cdot\|H\|\ \le\ E\ \le\ \|H\| .$$
--
--   This is the paper's main result for Quantum Max-Cut: an SDP-guided entangling circuit beats the $1/2$ barrier of product states on triangle-free graphs.
--
--   **Formalization Note** $E$ is the expectation of $\operatorname{Tr}(H\rho_{\mathrm{out}})$ over the Gaussian rounding matrix and the independent equator draws; $\|H\|$ is the maximum of $\langle\psi|H|\psi\rangle$ over unit vectors. The algorithm sees the instance only through the graph, $M$ and its random draws. The constant $0.582$ is the exact rational $582/1000$. The hypothesis on $\beta$ is how the proof uses $\beta^*$; it is satisfiable ($\beta=0.39$, milestone "display after Lemma 18"). "Efficient" and "classical description" in Theorem 3 are not formalized.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 3, Theorem 3; p. 16, Algorithm 17; p. 18, Theorem 19

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 3, Theorem 3, proved as Theorem 19, p. 18: on a triangle-free
weighted graph with total weight `1`, Algorithm 17 (p. 16) run on any optimal solution `M` of
`Lasserre_2(H)` (any Gram factorisation `W` of its `P_n^(1)` block for GP rounding) with any
`β ∈ [0, 1]` satisfying `F(β; x) ≥ 0.582 (1 + x)` on `[−1, 1]` (as `β* ≈ 0.390` does) has
expected output energy `E` with `0.582 · ‖H‖ ≤ E ≤ ‖H‖`. -/
theorem theorem_19 {n D : ℕ} (w : Fin n → Fin n → ℝ) (hw : IsWeightedGraph w)
    (hnorm : IsNormalized w) (htf : IsTriangleFree w)
    (M : Matrix (P2 n) (P2 n) ℝ) (hM : IsOptimal w M)
    (W : Fin n → Fin 3 → Fin D → ℝ) (hW : IsGramOfBlock M W)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hF : ∀ x ∈ Set.Icc (-1 : ℝ) 1, (582 / 1000 : ℝ) * (1 + x) ≤ Fβ β x) :
    (582 / 1000 : ℝ) * qmcValue w ≤ algEnergy w M W β ∧ algEnergy w M W β ≤ qmcValue w := by sorry

end QMCTriFree.Circuit
