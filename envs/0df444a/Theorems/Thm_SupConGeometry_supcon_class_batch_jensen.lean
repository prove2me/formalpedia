-- Prove2me | Theorems.Thm_SupConGeometry_supcon_class_batch_jensen
-- name    : SupConGeometry.supcon_class_batch_jensen
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:10:38.99209+00:00
-- url     : https://prove2.me/theorems/270fbec9-9838-4391-8374-7bb19679f3dd
-- title:
--   Lemma 1: Jensen bound for the class-specific batch-wise loss
-- statement:
--   Throughout, $h,N,K\in\mathbb N$ with $K\le h+1$, the batch size is $b\ge3$, $\rho>0$, and every $z_n$ lies on the sphere $\mathbb S^{h-1}_\rho=\{z\in\mathbb R^h:\|z\|=\rho\}$ (standing assumptions of Supplementary S1).
--
--   Fix a class $y$ and a batch $B\in\mathcal B$ with $|B_y|\in\{2,\dots,b\}$. Then for every labelling $Y$ the class-specific batch-wise loss satisfies
--
--   $$\ell_{SC}(Z;Y,B,y)\ \ge\ \sum_{i\in B_y}\log\Big(|B_y|-1+|B_y^C|\,\exp\big(S_i(Z;Y,B,y)\big)\Big).$$
--
--   Equality holds if and only if, for every $i\in B_y$:
--   1. (Q1) there is $C_i\in\mathbb R$ with $\langle z_i,z_j\rangle=C_i$ for every $j\in B_y\setminus\{\!\{i\}\!\}$;
--   2. (Q2) there is $D_i\in\mathbb R$ with $\langle z_i,z_j\rangle=D_i$ for every $j\in B_y^C$.
--
--   This is Step 1 of the proof of Theorem 2: Jensen's inequality for the exponential, applied separately to the same-class and other-class terms of the softmax denominator.
--
--   **Formalization Note** The sum over $i\in B_y$ counts multiplicity. When $|B_y|=b$ the complement is empty, the bound reads $b\log(b-1)$ and (Q2) holds trivially.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Supplementary S1.3, Lemma 1, eq. (35), p. 16; standing assumptions of Supplementary S1, p. 12

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_class_batch_jensen {N K h b : ℕ} (hKh : K ≤ h + 1) (hb : 3 ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ) (Y : Fin N → Fin K)
    (y : Fin K) (B : Sym (Fin N) b)
    (hB : 2 ≤ Multiset.card (batchClass Y (B : Multiset (Fin N)) y)) :
    ((batchClass Y (B : Multiset (Fin N)) y).map (fun i =>
        Real.log ((Multiset.card (batchClass Y (B : Multiset (Fin N)) y) : ℝ) - 1 +
          (Multiset.card (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ) *
            Real.exp (sInd Z Y B y i)))).sum ≤ scClassBatchLoss Z Y (B : Multiset (Fin N)) y ∧
    (scClassBatchLoss Z Y (B : Multiset (Fin N)) y =
        ((batchClass Y (B : Multiset (Fin N)) y).map (fun i =>
          Real.log ((Multiset.card (batchClass Y (B : Multiset (Fin N)) y) : ℝ) - 1 +
            (Multiset.card (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ) *
              Real.exp (sInd Z Y B y i)))).sum ↔
      ∀ i ∈ batchClass Y (B : Multiset (Fin N)) y,
        (∃ C : ℝ, ∀ j ∈ (batchClass Y (B : Multiset (Fin N)) y).erase i,
          inner ℝ (Z i) (Z j) = C) ∧
        (∃ D : ℝ, ∀ j ∈ batchClassCompl Y (B : Multiset (Fin N)) y, inner ℝ (Z i) (Z j) = D)) := by sorry

end SupConGeometry
