-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_symmetryReduction
-- name    : QAlgorithms.Papers.Independent.Information100.P58.symmetryReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:21:26.360487+00:00
-- url     : https://prove2.me/theorems/bbbaea0c-c752-4377-80cd-df84ecf1811d
-- title:
--   Symmetry reduction of the uniform basis ensemble
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For density operators $\omega,\sigma$ and $0\le\varepsilon<1$, define $\beta_\varepsilon(\omega\Vert\sigma)=\min\{\operatorname{Tr}(T\sigma):0\le T\le I,\operatorname{Tr}(T\omega)\ge1-\varepsilon\}$ and $D_H^\varepsilon=-\log_2\beta_\varepsilon$, with $-\log_2 0=+\infty$. Let $X$ label all $d^n$ computational-basis words uniformly, $\pi_X=I_X/d^n$, and $\Theta_{XB}=d^{-n}\sum_x|x\rangle\langle x|\otimes\mathcal E_p^{\otimes n}(|x\rangle\langle x|)$. Put $\omega_0=\mathcal E_p^{\otimes n}((|0\rangle\langle0|)^{\otimes n})$ and $\sigma_q=\bigoplus_S q_S I_S/D_S$. Then
--
--   $$\inf_{\sigma}D_H^\varepsilon(\Theta_{XB}\Vert\pi_X\otimes\sigma)=\inf_qD_H^\varepsilon(\omega_0\Vert\sigma_q).$$
--
--   The left infimum ranges over all output density matrices, and the right over all probability distributions on survivor sets. This evaluates the source-constructed basis ensemble, with no free ensemble parameter.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 45, Appendix A, Eq. (A.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Appendix A, Eq.(A.2), PDF pp.45–46: symmetry reduction for the constructed uniform basis ensemble. -/
theorem symmetryReduction (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1) :
    basisEnsembleInf n d p ε =
      ⨅ q : Distribution (Finset (Fin n)),
        testingD ε (erasure n d p (basisDensity (fun _ : Fin n => (⟨0, by omega⟩ : Fin d))))
          (auxiliary n d q.val) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
