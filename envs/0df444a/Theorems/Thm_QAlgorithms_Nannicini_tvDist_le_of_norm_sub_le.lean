-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_tvDist_le_of_norm_sub_le
-- name    : QAlgorithms.Nannicini.tvDist_le_of_norm_sub_le
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:18.772135+00:00
-- url     : https://prove2.me/theorems/e5b22f49-db09-4465-baf9-1c3b4fe69992
-- title:
--   Close states give close measurement distributions
-- statement:
--   Let $q\ge0$ and let $|\psi\rangle=\sum_{\vec\jmath\in\{0,1\}^q}\alpha_j|\vec\jmath\rangle$ and $|\phi\rangle=\sum_{\vec\jmath\in\{0,1\}^q}\beta_j|\vec\jmath\rangle$ be two $q$-qubit quantum states, i.e. unit vectors. Measuring all qubits of $|\psi\rangle$ gives outcome $\vec\jmath$ with probability $p_j=|\alpha_j|^2$, and for $|\phi\rangle$ with probability $q_j=|\beta_j|^2$. Call these distributions $P$ and $Q$, and let $d_{TV}(P,Q)=\frac12\sum_j|p_j-q_j|$ be their total variation distance (Def. 1.47). Let $\epsilon\in\mathbb R$. If $\||\psi\rangle-|\phi\rangle\|\le\epsilon$ in the Euclidean norm, then
--
--   $$
--   d_{TV}(P,Q)\le\epsilon .
--   $$
--
--   So two states that are close in Euclidean norm give almost the same measurement statistics. Together with Proposition 1.46, this justifies measuring circuit approximations in the operator norm.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 31, Proposition 1.49. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms




/-- Nannicini, Proposition 1.49, PDF pp. 31–32. Let `|ψ⟩ = Σ_j α_j |j⟩` and `|ϕ⟩ = Σ_j β_j |j⟩` be
two quantum states on `q` qubits, and let `P`, `Q` be the distributions over `{0,1}^q` obtained
by measuring all qubits (`P(j) = |α_j|²`, `Q(j) = |β_j|²`, Prop. 1.27). If
`‖|ψ⟩ − |ϕ⟩‖ ≤ ϵ`, then `d_TV(P, Q) ≤ ϵ`, with `d_TV(P, Q) = (1/2) Σ_j |p_j − q_j|`
(Def. 1.47). -/
theorem tvDist_le_of_norm_sub_le (q : ℕ) (ψ φ : EuclideanSpace ℂ (Qubits q))
    (hψ : IsState ψ) (hφ : IsState φ) (ε : ℝ) (h : ‖ψ - φ‖ ≤ ε) :
    tvDist (prob ψ) (prob φ) ≤ ε := by
  sorry

end QAlgorithms.Nannicini
