-- Prove2me | Theorems.Thm_QuaternionAlgebra_nrd_eq_det_of_ringEquiv
-- name    : QuaternionAlgebra.nrd_eq_det_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/a8f00a22-76b2-51eb-a36b-64874a2813c4
-- title:
--   Reduced norm equals determinant under any scalar-fixing splitting
-- statement:
--   Let $a,b$ be rational numbers, let $v$ be a height one prime of the ring of integers of $\mathbb{Q}$, and write $\mathbb{Q}_v$ for the $v$-adic completion of $\mathbb{Q}$. Suppose given two ring isomorphisms out of the base change $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ of the quaternion algebra with parameters $a,b$: first, $\varphi$ onto the $2\times 2$ matrix ring $M_2(\mathbb{Q}_v)$, assumed to satisfy $\varphi(1\otimes r)=r\cdot 1$ for every $r\in\mathbb{Q}_v$; second, $\psi$ onto the quaternion algebra $\mathbb{H}[\mathbb{Q}_v,a,b]$ over $\mathbb{Q}_v$ whose parameters are the images of $a$ and $b$ under the structure map $\mathbb{Q}\to\mathbb{Q}_v$, assumed to satisfy $\psi(z\otimes r)=r\cdot(z_0,z_1,z_2,z_3)$ for all $z\in\mathbb{H}[\mathbb{Q},a,b]$ and $r\in\mathbb{Q}_v$, where $z_0,z_1,z_2,z_3$ denote the images in $\mathbb{Q}_v$ of the four coordinates of $z$. Then for every $x$ in $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ one has $\mathrm{nrd}(\psi(x))=\det(\varphi(x))$, where $\mathrm{nrd}(y)=y_0^2-a\,y_1^2-b\,y_2^2+ab\,y_3^2$ is the reduced norm of the quaternion $y$ (with $a,b$ read in $\mathbb{Q}_v$).
--
--   This identifies the reduced norm of a quaternion algebra over $\mathbb{Q}$, computed in coordinates after base change to a completion, with the determinant obtained from an arbitrary local splitting, subject only to the normalisation that the splitting be the identity on scalars; no compatibility between $\varphi$ and $\psi$ beyond this is assumed. It is used in the study of maximal orders in such algebras, in the construction of elements of reduced norm one in a prescribed local neighbourhood.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_nrd_eq_det_of_ringEquiv.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.nrd_eq_det_of_ringEquiv
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
    (hψ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      ψ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
        algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
        algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    QuaternionAlgebra.nrd (ψ x) = (φ x).det := by sorry
