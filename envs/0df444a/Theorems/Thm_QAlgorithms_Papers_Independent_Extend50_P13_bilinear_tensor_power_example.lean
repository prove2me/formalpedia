-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_bilinear_tensor_power_example
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.bilinear_tensor_power_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:42:50.91563+00:00
-- url     : https://prove2.me/theorems/0f7077cf-15ea-44fd-a8c1-5a30d7a6cf70
-- title:
--   Example 14 / Eqs.(49)–(51): bilinear tensor-power inequality
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. For $\lambda=(2,1)$, $f_\lambda(X,Y)=[2\operatorname{tr}(X)\operatorname{tr}(Y)I-XY-YX]/3$. Let $\rho,\mu$ be density matrices on $H=\bigotimes_{j=1}^n\mathbb C^{d_j}$, $d_j\ge1$, $n\ge0$. Write $\rho_S=\operatorname{tr}_{S^c}\rho$, use $T_A$ for partial transpose on $A\subseteq S$, and $\iota_S$ for identity embedding in the original positions. Then
--
--   $$f_\lambda^{\otimes n}(\rho,\mu)=\left(\frac23\right)^n\sum_{S\subseteq[n]}\sum_{A\subseteq S}\left(-\frac12\right)^{|S|}\iota_S\left[(\rho_S^{T_A}\mu_S^{T_A})^{T_A}\right]\ge0.$$
--
--   For two parties, writing $\{B,C\}=BC+CB$ and $\rho_j,\mu_j$ for the single-party reductions, this is also
--
--   $$\frac19\left[4I+(\rho^{T_1}\mu^{T_1})^{T_1}+(\rho^{T_2}\mu^{T_2})^{T_2}-2\bigl(\{\rho_1,\mu_1\}\otimes I+I\otimes\{\rho_2,\mu_2\}\bigr)+\{\rho,\mu\}\right].$$
--
--   Tensor powers use the vertical-projector contraction. The complete sum is PSD; individual products are not asserted Hermitian.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 12, Example 14 / Eqs.(49)–(51): bilinear tensor-power inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Example 14, Eqs.49–51 (PDF p.12). SOURCE CORRECTION: Eq.51 prints (3/2)^n;
its prefactor must be (2/3)^n, as Eq.50, n=1, and the 4/9 empty-subset term in
Eq.49 all require. Individual partially transposed products are not asserted PSD.
The normalized one-party map, bipartite expansion and all-party expansion are included. -/
theorem bilinear_tensor_power_example
    (lambda : QAlgorithms.Schur.Partition 3 3) (hshape : lambda.val.rowLens = [2,1]) :
    (∀ (d : ℕ), 0 < d → ∀ X Y : (Matrix (Fin d) (Fin d) ℂ),
      polarizedMap lambda ![X,Y] = (1/3 : ℂ) • mixedThree X Y) ∧
    (∀ (dims : Fin 2 → ℕ), (∀ j, 0 < dims j) →
      ∀ rho mu : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ), QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix mu →
        mixedMap dims (fun _ => lambda) ![rho,mu] = bipartiteExpansion dims rho mu ∧
        (bipartiteExpansion dims rho mu).PosSemidef) ∧
    (∀ (n : ℕ) (dims : Fin n → ℕ), (∀ j, 0 < dims j) →
      ∀ rho mu : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ), QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix mu →
        mixedMap dims (fun _ => lambda) ![rho,mu] = bilinearExpansion dims rho mu ∧
        (bilinearExpansion dims rho mu).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
