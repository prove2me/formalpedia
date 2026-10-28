-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_actualMarginalStrongConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P67.actualMarginalStrongConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:03:55.003758+00:00
-- url     : https://prove2.me/theorems/cfec62bc-d052-40cc-a747-cff4c1e778d7
-- title:
--   Corollary D.2 (Exponential strong converse with the actual marginal)
-- statement:
--   Fix a finite-dimensional channel dilation and any threshold $q$, positive gap $\Delta$, positive exponent $\gamma$, and blocklength threshold $n_0$. Suppose these particular witnesses give $f(\mathcal C_n)\le2^{-\gamma n}$ for every valid code with $n\ge n_0$ and $\log_2M\ge n(q+\Delta)$. The identical witnesses then give
--
--   $$f_{\rm marg}(\mathcal C_n)\le2^{-\gamma n},\qquad \varepsilon_{\rm marg}(\mathcal C_n)\ge1-2^{-\gamma n}$$
--
--   for every code under precisely the same conditions. Taking $q=q_{\mathcal N}$ gives the degradable conclusion, and the same implication applies to the antidegradable and erasure thresholds. This states the source's same-constants transfer, without selecting fresh witnesses.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 47, Corollary D.2 (Exponential strong converse with the actual marginal)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Corollary D.2, PDF pp.47–48: any witnesses transfer unchanged.
The arbitrary threshold also covers the antidegradable and erasure cases. -/
theorem actualMarginalStrongConverse [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (q gap gamma : ℝ) (hgap : 0 < gap) (hgamma : 0 < gamma) (n0 : ℕ)
    (hdecay : OptimizedDecay U q gap gamma n0) :
    ∀ n ≥ n0, ∀ code : PrivateCode A B n, code.Valid →
      (n : ℝ) * (q + gap) ≤ Real.logb 2 code.M →
      marginalFidelity U code ≤ Real.rpow 2 (-gamma * n) ∧
      1 - Real.rpow 2 (-gamma * n) ≤ marginalError U code := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
