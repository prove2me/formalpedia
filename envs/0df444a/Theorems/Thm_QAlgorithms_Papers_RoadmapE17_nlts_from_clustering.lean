-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapE17_nlts_from_clustering
-- name    : QAlgorithms.Papers.RoadmapE17.nlts_from_clustering
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:34:44.656842+00:00
-- url     : https://prove2.me/theorems/406af229-5e99-4912-a0e9-2c5498ccc75f
-- title:
--   NLTS from clustering CSS codes: logarithmic depth for all low-energy states
-- statement:
--   Fix positive clustering constants $c_1,c_2,\delta_0$, a bound $s$ on the number of nonzero entries in each row and column of the binary check matrices, and a positive constant $B$ bounding the total number of checks by $Bn$. There exist $a>0$ and an integer $n_0\ge2$, uniform over the code, state, energy density and preparing circuit, with the following property.
--
--   For $n\ge n_0$, let $H_x\in\mathbb F_2^{m_x\times n}$ and $H_z\in\mathbb F_2^{m_z\times n}$ be check matrices with $m_x,m_z>0$, sparsity at most $s$, and $m_x+m_z\le Bn$. Put $C_x=\ker H_x$ and $C_z=\ker H_z$, and assume the CSS condition $C_x^\perp\subseteq C_z$. Write $k$ for the encoded dimension, and assume $k\ge2$. Assume Property 1: for every $0\le\delta<\delta_0$ and every $y\in\mathbb F_2^n$, $|H_z y|\le\delta m_z$ implies $|y|_{C_x^\perp}\le c_1\delta n$ or $|y|_{C_x^\perp}\ge c_2n$, and the same implication holds with $x,z$ interchanged. Here $|y|_S=\min_{v\in S}|y+v|$, and $|\cdot|$ is Hamming weight. Define the unnormalized check Hamiltonian $H=\sum_{w\text{ row of }H_x}(I-X^w)/2+\sum_{w\text{ row of }H_z}(I-Z^w)/2$, counting all supplied rows.
--
--   Define
--   $$
--   E(C)=\frac{1}{400c_1}\frac{\min\{m_x,m_z\}}{n}\min\left\{\left(\frac{k-1}{4n}\right)^2,\delta_0,\frac{c_2}{2}\right\}.
--   $$
--   The corrected permitted cutoff is
--   $$
--   E_{\mathrm{eff}}(C)=\min\{E(C),\delta_0\min(m_x,m_z)/(400n)\}.
--   $$
--   For every density matrix $\rho$ and every $0\le\epsilon<E_{\mathrm{eff}}(C)$,
--   $$
--   \operatorname{tr}(H\rho)\le\epsilon n
--   \quad\Longrightarrow\quad
--   \operatorname{depth}(U)\ge a\log n
--   $$
--   for every preparing circuit $U$. A preparing circuit consists of layers of disjoint arbitrary one- and two-qubit unitary gates on $n+w$ qubits, for any $w\ge0$, starts in $|0\rangle^{\otimes(n+w)}$, and has reduced output $\rho$ on the first $n$ qubits after discarding the other qubits. Depth is its number of layers; $\log$ is the natural logarithm.
--
--   Moreover, for every fixed $r,q>0$, there exist $e_*>0$ and $n_1\ge2$, uniform over all code instances, such that whenever $n\ge n_1$, $k\ge rn$ and $\min\{m_x,m_z\}\ge qn$, one has
--   $$
--   k\ge2,\qquad E_{\mathrm{eff}}(C)\ge e_*.
--   $$
--   Consequently the allowed energy density can be chosen as a positive constant for the constant-rate, linear-distance qLDPC families satisfying Property 1 considered in the paper. The distance parameter does not enter the displayed cutoff; the paper's footnote 3 notes that Property 1 at $\delta=0$ already implies linear distance.
--
--   This gives a depth obstruction for every low-energy density matrix, including mixed states, rather than only ground states.
--
--   **Source correction.** The paper prints only $\epsilon<E(C)$. Its proof uses Property 1 at $2\epsilon_1$ with $\epsilon_1=200n\epsilon/\min(m_x,m_z)$, so we also require $400n\epsilon<\delta_0\min(m_x,m_z)$. This is exactly the missing domain condition; it is automatic if $c_1\ge1$. No normalization $c_1\ge1$ is imposed, and the frozen printed cutoff is retained as the first entry of the minimum.
--
--   **Correction to the printed source.**
--
--   Printed: Theorem 5 permits eps < E(C), where E(C) is the printed energyCutoff, for arbitrary positive c1.
--
--   Corrected: Use eps < min(E(C), delta0*min(mx,mz)/(400*n)); give the eventual positive floor for this same minimum. No other hypothesis, constant, or conclusion is changed.
--
--   Reason: The source proof sets epsilon1=200*n*eps/min(mx,mz) on p.3 and applies Property 1 at 2*epsilon1 on p.4. Its domain is delta<delta0, but the printed cutoff only supplies 2*c1*epsilon1<delta0. The additional strict upper bound is exactly 2*epsilon1<delta0. It is redundant for c1>=1 and retains every c1<1 instance satisfying the actual proof-domain condition.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Theorem 5 (Formal statement of the NLTS theorem), §2, PDF p. 5. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapE17

open QAlgorithms.NLTS QAlgorithms.PresentedCSS

/-- Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4, Theorem 5, PDF p.5,
with Property 1 and the check Hamiltonian of p.2 and the preparation model of p.9.
The first clause spells out the uniform meaning of Omega(log n); the second gives
a positive eventual lower bound on the permitted energy-density cutoff at positive
rate and positive check density. Distance does not occur in that cutoff (footnote 3).

Printed: eps < energyCutoff C positive c1 c2 delta0 hc1. Changed: also require
eps < delta0 * min(mx,mz) / (400*n), expressed as the minimum of the two cutoffs.
Why: p.3 sets epsilon1 = 200*n*eps/min(mx,mz), and p.4 applies Property 1
at 2*epsilon1. The printed formula only ensures 2*c1*epsilon1 < delta0;
the added condition supplies exactly 2*epsilon1 < delta0 without assuming c1 >= 1.
The eventual positive floor is bounded by the same minimum. This is the sole
source correction; the frozen printed energyCutoff is unchanged. -/
theorem nlts_from_clustering
    (c1 c2 delta0 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hdelta0 : 0 < delta0)
    (sparsity : ℕ) (checkUpper : ℝ) (hcheckUpper : 0 < checkUpper) :
    (∃ depthConstant : ℝ, 0 < depthConstant ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ mx mz : ℕ,
      ∀ C : CheckPresentation n mx mz,
      ∀ positive : 0 < n ∧ 0 < mx ∧ 0 < mz,
      HasSparsity C.HX sparsity → HasSparsity C.HZ sparsity →
      ((mx + mz : ℕ) : ℝ) ≤ checkUpper * n →
      ClustersApproximateCodewords C c1 c2 delta0 →
      2 ≤ C.logicalDimension →
      ∀ eps : ℝ, 0 ≤ eps → eps < min (energyCutoff C positive c1 c2 delta0 hc1)
        (delta0 * ((min mx mz : ℕ) : ℝ) / (400 * n)) →
      ∀ rho : Matrix (Qubits n) (Qubits n) ℂ, IsDensityMatrix rho →
      (cssCheckHamiltonian C * rho).trace.re ≤ eps * n →
      ∀ circuit : LayeredPreparationCircuit n,
      preparationOutputDensity circuit = rho →
        depthConstant * Real.log n ≤ (preparationDepth circuit : ℝ)) ∧
    (∀ rate checkDensity : ℝ, 0 < rate → 0 < checkDensity →
      ∃ energyFloor : ℝ, 0 < energyFloor ∧ ∃ n1 : ℕ, 2 ≤ n1 ∧
      ∀ n : ℕ, n1 ≤ n → ∀ mx mz : ℕ,
      ∀ C : CheckPresentation n mx mz,
      ∀ positive : 0 < n ∧ 0 < mx ∧ 0 < mz,
      rate * n ≤ (C.logicalDimension : ℝ) →
      checkDensity * n ≤ ((min mx mz : ℕ) : ℝ) →
        2 ≤ C.logicalDimension ∧
        energyFloor ≤ min (energyCutoff C positive c1 c2 delta0 hc1)
          (delta0 * ((min mx mz : ℕ) : ℝ) / (400 * n))) := by sorry

end QAlgorithms.Papers.RoadmapE17
