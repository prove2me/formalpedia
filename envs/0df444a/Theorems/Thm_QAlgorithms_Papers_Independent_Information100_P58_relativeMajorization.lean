-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_relativeMajorization
-- name    : QAlgorithms.Papers.Independent.Information100.P58.relativeMajorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:13:48.120352+00:00
-- url     : https://prove2.me/theorems/0fa21eac-21d7-436f-8b39-f50e8813fc3c
-- title:
--   Simultaneous relative majorization of erasure outputs
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For a unit vector $\psi\in\mathbb C^d$, put $\omega_\psi=\mathcal E_p^{\otimes n}((|\psi\rangle\langle\psi|)^{\otimes n})$. For a probability distribution $q=(q_S)$ on all survivor sets, including the empty set, put $\sigma_q=\bigoplus_S q_S I_S/D_S$. For every input density operator $\rho$ on all $n$ inputs, there exists a completely positive trace-preserving map $\mathcal M_\rho$ on the full output space such that
--
--   $$\mathcal M_\rho(\omega_\psi)=\mathcal E_p^{\otimes n}(\rho),\qquad \mathcal M_\rho(\sigma_q)=\sigma_q\quad\text{for every }q.$$
--
--   The map may depend on $\psi$ and $\rho$, but a single map preserves the entire auxiliary family. This is a channel conversion, including the empty scalar sector.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 19, Theorem 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Theorem 5.1, PDF pp.19–20: one channel converts the reference output and fixes every auxiliary. -/
theorem relativeMajorization (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1)
    (ρ : Operator (Word n d)) (hρ : IsDensityMatrix ρ) :
    ∃ Φ : Superop (Output n d) (Output n d), IsChannel Φ ∧
      Φ (reference n d p ψ) = erasure n d p ρ ∧
      ∀ q : Distribution (Finset (Fin n)), Φ (auxiliary n d q.val) = auxiliary n d q.val := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
