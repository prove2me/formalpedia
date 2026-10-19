-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapX03_holevo_entanglementBreaking
-- name    : QAlgorithms.Papers.RoadmapX03.holevo_entanglementBreaking
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:16:08.621993+00:00
-- url     : https://prove2.me/theorems/69743ab5-dd82-4e69-91c7-22052476e041
-- title:
--   Positive Holevo maps break entanglement, with the CPT channel specialization
-- statement:
--   Let $d\ge 1$ and $m\ge 0$ be integers. Fix density matrices $R_1,\ldots,R_m\in M_d(\mathbb C)$ and positive semidefinite matrices $F_1,\ldots,F_m\in M_d(\mathbb C)$, and define the complex-linear Holevo map on all matrices by
--
--   $$
--   \Phi(X)=\sum_{k=1}^m R_k\operatorname{Tr}(F_kX).
--   $$
--   For every positive finite reference dimension $a$ and every density matrix $\Gamma$ on $\mathbb C^a\otimes\mathbb C^d$,
--
--   $$
--   (\mathrm{id}_a\otimes\Phi)(\Gamma)\in\operatorname{cone}\{A\otimes B:A\text{ and }B\text{ are density matrices}\}.
--   $$
--   Here the cone consists of finite sums with nonnegative real coefficients and includes zero. If, in addition, $\{F_k\}_{k=1}^m$ is a POVM, meaning $\sum_kF_k=I_d$, then $\Phi$ is completely positive and trace-preserving, and every such joint output is a separable density matrix: it is a finite convex combination of product density matrices.
--
--   This is precisely the measure-and-prepare implication of Theorem 4 and its printed channel specialization. It applies to entangled inputs without purity, orthogonality, or independence restrictions on the prepared states.
--
--   **Formalization Note** The general part uses the frozen separable-positive-cone predicate because unrestricted positive effects need not preserve trace. The channel part uses normalized separability. The identity always acts on the reference factor.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, §2, Theorem 4(A) ⇒ (B); trace-preserving continuation and proof, PDF p.5; eq.(1), PDF p.2, PDF p. 4. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
set_option autoImplicit false

open scoped ComplexOrder

namespace QAlgorithms.Papers.RoadmapX03

/-- Horodecki, Shor and Ruskai, arXiv:quant-ph/0302031v2, Theorem 4(A) ⇒ (B),
PDF pp.4–5; Holevo form (1) and Definition 1, PDF p.2.
For positive effects the joint output belongs to the separable positive cone,
including zero. When the effects form a POVM, the same computed map is a CPT
channel and every joint density input has a normalized separable output.
The identity acts on the first (reference) factor, of arbitrary positive finite
dimension. No purity or independence of the prepared density matrices is assumed. -/
theorem holevo_entanglementBreaking (d m : ℕ) (hd : 0 < d)
    (R F : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef) :
    Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) ∧
      (IsPOVM F → IsChannel (Entanglement.holevoMap R F) ∧
        ∀ (a : ℕ) (ha : 0 < a),
          letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
          letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
          ∀ Gamma : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ,
            IsDensityMatrix Gamma →
              Entanglement.IsSeparableDensity
                (idTensorSuperop (Entanglement.holevoMap R F) Gamma)) := by sorry

end QAlgorithms.Papers.RoadmapX03
