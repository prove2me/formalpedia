-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_pgm_agnostic_hard_ensemble
-- name    : QAlgorithms.Arunachalam.pgm_agnostic_hard_ensemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:57:02.908946+00:00
-- url     : https://prove2.me/theorems/d7edc4ec-185f-45dc-a05b-3d2d0a93ac04
-- title:
--   PGM success bound for the agnostic hard ensemble
-- statement:
--   Fix integers $d\ge 10$, $k$ and $T\ge 1$ and a real $\varepsilon\in(0,1/10)$. Let $M\in\mathbb F_2^{d\times k}$ have rank $k$ with $k\ge d/4$ and $d_H(Mx,My)\ge d/8$ for $x\ne y$. For $x\in\{0,1\}^k$ let $D_x$ be the distribution on $[d]\times\{0,1\}$
--
--   $$
--   D_x(s_i,b)=\frac1d\left(\frac12+(-1)^{(Mx)_i+b}\,\frac{\alpha}{2}\right),\qquad \alpha=10\varepsilon,
--   $$
--
--   and assume $T\le d/(100e^3\varepsilon^2)$. Put $|\psi_x\rangle=\sum_{(i,b)\in[d]\times\{0,1\}}\sqrt{D_x(s_i,b)}\,|s_i,b\rangle$ and $\mathcal E=\{(2^{-k},|\psi_x\rangle^{\otimes T}):x\in\{0,1\}^k\}$. Then
--
--   $$
--   P^{\mathrm{PGM}}(\mathcal E)\ \le\ \frac{4e}{e^{(d\ln 2)/4+25T\varepsilon^2}}\;e^{220000\,T^2\varepsilon^4/d+20\sqrt{Td\varepsilon^2}}.
--   $$
--
--   This is the state-identification bound behind Theorem 7.5.8: identifying $x$ with constant probability needs $T=\Omega(d/\varepsilon^2)$ copies.
--
--   **Formalization Note** $\alpha=10\varepsilon$ is the value the lemma's own proof computes with (the factors $1+10\varepsilon(-1)^{(Mx)_i+b}$ and $\beta=1-\sqrt{1-100\varepsilon^2}$); the surrounding text's $\alpha=20\varepsilon$ is a recorded discrepancy. The points $s_i$ are orthonormal labels $i\in[d]$. The last exponent term, garbled in extraction, is read as $20\sqrt{Td\varepsilon^2}$, i.e. $2\sqrt{Td\beta}$ with $\beta\le100\varepsilon^2$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 179, Lemma 7.5.9. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning




/-- Arunachalam p.178–180, Lemma 7.5.9, in the setting of the proof of Theorem 7.5.8:
`ε ∈ (0, 1/10)`; `M ∈ F₂^{d×k}` is the rank-`k` generator matrix of a `[d, k, r]₂` code with
`k ≥ d/4` and `r ≥ d/8`; `D_x(s_i, b) = (1/d)(1/2 + (−1)^{(Mx)_i + b} α/2)` on `[d] × {0,1}` with
`α = 10ε` (the value the lemma's proof computes with; recorded discrepancy with the text's
`α = 20ε`); `1 ≤ T ≤ d/(100e³ε²)` and `d ≥ 10` (Theorem 7.5.1 with `m = d`,
`β = 1 − √(1 − 100ε²)`). For `x ∈ {0,1}^k` let
`|ψ_x⟩ = ∑_{(i,b) ∈ [d]×{0,1}} √D_x(s_i, b) |s_i, b⟩` and `E = {(2^{−k}, |ψ_x⟩^{⊗T})}`. Then
`P^PGM(E) ≤ (4e / e^{(d ln 2)/4 + 25Tε²}) e^{220000T²ε⁴/d + 20√(Tdε²)}`. -/
theorem pgm_agnostic_hard_ensemble {d k T : ℕ} {ε : ℝ} (hd : 10 ≤ d) (hε : 0 < ε)
    (hε' : ε < 1 / 10) (M : Matrix (Fin d) (Fin k) (ZMod 2)) (hM : M.rank = k) (hkd : k ≤ d)
    (hdk : d ≤ 4 * k)
    (hdist : ∀ x y : Fin k → ZMod 2, x ≠ y →
      (d : ℝ) / 8 ≤ (hammingDist (M.mulVec x) (M.mulVec y) : ℝ))
    (hT : 1 ≤ T) (hTd : (T : ℝ) ≤ (d : ℝ) / (100 * Real.exp 3 * ε ^ 2)) :
    pgmSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
        (fun x => tensorPow T (agnosticExampleState (agnHardDist M ε x))) ≤
      4 * Real.exp 1 / Real.exp ((d : ℝ) * Real.log 2 / 4 + 25 * (T : ℝ) * ε ^ 2) *
        Real.exp (220000 * (T : ℝ) ^ 2 * ε ^ 4 / (d : ℝ) +
          20 * Real.sqrt ((T : ℝ) * (d : ℝ) * ε ^ 2)) := by
  sorry



end QAlgorithms.Arunachalam
