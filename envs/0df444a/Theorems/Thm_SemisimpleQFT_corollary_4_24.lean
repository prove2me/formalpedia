-- Prove2me | Theorems.Thm_SemisimpleQFT_corollary_4_24
-- name    : SemisimpleQFT.corollary_4_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:13:15.848108+00:00
-- url     : https://prove2.me/theorems/5c529f42-7b26-4453-ae89-fd9f21275b6b
-- title:
--   Corollary 4.24: $\|E^\rho_{ij}\|_2^2\cdot d^n/m_\rho=1\pm O(d^{-1/2}|A|)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $A\in\{P_n(d),P_{n-1/2}(d),B_n(d),B_{r,s}(d)\}$ with its scaled diagram basis $\mathcal B(A)$, and take a Fourier basis of $A$ in the orthogonal form ($\rho(D^{\mathrm{op}})=\rho(D)^\dagger$, the convention under which Lemma 4.19 holds). Let $m_\rho$ be the multiplicity of $\rho$ in the Schur representation. If $d^{-1/2}|A|\le1/2$, then for all $\rho,i,j$:
--
--   1. $\left|\,\|E^\rho_{ij}\|_2^2\cdot\dfrac{d^n}{m_\rho}-1\right|\le C\,d^{-1/2}|A|$;
--   2. $\left|\,\|E^\rho_{ij}\|_2\cdot\sqrt{\dfrac{d^n}{m_\rho}}-1\right|\le C\,d^{-1/2}|A|$.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 29, Corollary 4.24 (with Lemma 4.19 and Corollary 4.23)

import Definitions.Def_SemisimpleQFT_Diagram

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem corollary_4_24 :
    ∃ C : ℝ, ∀ (n d : ℕ) (S : Set (Diagram n)) (Λ J : Type) [Fintype J] [DecidableEq J]
      (F : FourierData (diagramAlgebra S d) Λ J),
      IsStdFamily n d S → IsOrthogonalForm F →
      (Nat.card S : ℝ) / Real.sqrt (d : ℝ) ≤ 1 / 2 →
      ∀ i j : J, F.lab i = F.lab j →
        |(diagBasis S d).norm (F.E i j) ^ 2 * ((d : ℝ) ^ n / (schurMult F i : ℝ)) - 1| ≤
            C * (Nat.card S : ℝ) / Real.sqrt (d : ℝ) ∧
        |(diagBasis S d).norm (F.E i j) * Real.sqrt ((d : ℝ) ^ n / (schurMult F i : ℝ)) - 1| ≤
            C * (Nat.card S : ℝ) / Real.sqrt (d : ℝ) := by sorry

end SemisimpleQFT
