-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_pgm_pac_hard_ensemble
-- name    : QAlgorithms.Arunachalam.pgm_pac_hard_ensemble
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:56:28.148609+00:00
-- url     : https://prove2.me/theorems/4a017594-c5e9-412f-8f4b-e3ceb48d1ef4
-- title:
--   PGM success bound for the PAC hard ensemble
-- statement:
--   Fix integers $d\ge 10$, $k$ and $T\ge 1$ and a real $\varepsilon\in(0,1/20)$. Let $M\in\mathbb F_2^{d\times k}$ be a matrix of rank $k$ with $k\ge d/4$ whose codewords satisfy $d_H(Mx,My)\ge d/8$ for $x\neq y$ (the generator matrix of a $[d,k,r]_2$ code with $r\ge d/8$). On the points $s_0,\dots,s_d$ let $D(s_0)=1-20\varepsilon$ and $D(s_i)=20\varepsilon/d$ for $i\in[d]$, and for $x\in\{0,1\}^k$ let $c^x(s_0)=0$ and $c^x(s_i)=(Mx)_i$. Assume $T\le d/(20e^3\varepsilon)$. Put
--
--   $$
--   |\psi_x\rangle=\sum_{i=0}^{d}\sqrt{D(s_i)}\,|s_i,c^x(s_i)\rangle,\qquad \mathcal E=\{(2^{-k},|\psi_x\rangle^{\otimes T}):x\in\{0,1\}^k\}.
--   $$
--
--   Then the success probability of the pretty good measurement for $\mathcal E$ satisfies
--
--   $$
--   P^{\mathrm{PGM}}(\mathcal E)\ \le\ \frac{4e}{2^{d/4+T\varepsilon}}\;e^{8800T^2\varepsilon^2/d+4\sqrt{5Td\varepsilon}}.
--   $$
--
--   Since the PGM is optimal for this ensemble, the bound shows that $T=\Omega(d/\varepsilon)$ copies are needed to identify $x$ with constant probability; it is the core of Theorem 7.5.6.
--
--   **Formalization Note** The points $s_i$ enter only as orthonormal labels, so $|s_i,b\rangle$ is the basis vector of $(i,b)\in\{0,\dots,d\}\times\{0,1\}$. $P^{\mathrm{PGM}}(\mathcal E)=\sum_x p_x|\langle\psi_x'|\rho^{-1/2}|\psi_x\rangle|^2$ with $\rho=\sum_x|\psi_x'\rangle\langle\psi_x'|$, $\psi_x'=\sqrt{p_x}\psi_x$ (pseudo-inverse square root). The hypotheses $d\ge 10$, $T\ge1$, $T\le d/(20e^3\varepsilon)$ and the code parameters are those of the surrounding proof (Theorem 7.5.1 with $m=d$, $\beta=20\varepsilon$).
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 176, Lemma 7.5.7. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning


/-- Arunachalam p.176–177, Lemma 7.5.7, in the setting of the proof of Theorem 7.5.6:
`ε ∈ (0, 1/20)`; `D(s₀) = 1 − 20ε`, `D(s_i) = 20ε/d` for `i ∈ [d]`; `M ∈ F₂^{d×k}` is the rank-`k`
generator matrix of a `[d, k, r]₂` code with `k ≥ d/4` and distance `r ≥ d/8`; `c^x(s₀) = 0`,
`c^x(s_i) = (Mx)_i`; `1 ≤ T ≤ d/(20e³ε)` and `d ≥ 10` (the hypotheses of Theorem 7.5.1 with
`m = d`, `β = 20ε`). For every `x ∈ {0,1}^k` let `|ψ_x⟩ = ∑_{i ∈ {0,…,d}} √D(s_i) |s_i, c^x(s_i)⟩`
and `E = {(2^{−k}, |ψ_x⟩^{⊗T}) : x ∈ {0,1}^k}`. Then
`P^PGM(E) ≤ (4e / 2^{d/4 + Tε}) e^{8800T²ε²/d + 4√(5Tdε)}`. -/
theorem pgm_pac_hard_ensemble {d k T : ℕ} {ε : ℝ} (hd : 10 ≤ d) (hε : 0 < ε) (hε' : ε < 1 / 20)
    (M : Matrix (Fin d) (Fin k) (ZMod 2)) (hM : M.rank = k) (hkd : k ≤ d) (hdk : d ≤ 4 * k)
    (hdist : ∀ x y : Fin k → ZMod 2, x ≠ y →
      (d : ℝ) / 8 ≤ (hammingDist (M.mulVec x) (M.mulVec y) : ℝ))
    (hT : 1 ≤ T) (hTd : (T : ℝ) ≤ (d : ℝ) / (20 * Real.exp 3 * ε)) :
    pgmSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
        (fun x => tensorPow T (exampleState (pacHardConcept M x) (pacHardDist d ε))) ≤
      4 * Real.exp 1 / (2 : ℝ) ^ ((d : ℝ) / 4 + (T : ℝ) * ε) *
        Real.exp (8800 * (T : ℝ) ^ 2 * ε ^ 2 / (d : ℝ) +
          4 * Real.sqrt (5 * (T : ℝ) * (d : ℝ) * ε)) := by
  sorry





end QAlgorithms.Arunachalam
