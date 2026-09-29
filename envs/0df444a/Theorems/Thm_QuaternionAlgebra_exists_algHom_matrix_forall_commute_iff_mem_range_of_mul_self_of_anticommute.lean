-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute
-- name    : QuaternionAlgebra.exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/4c80b8d9-c571-5b1f-81b4-949bc125e6ff
-- title:
--   Commutant of an embedded quaternion pair is the symbol algebra (t,sc')
-- statement:
--   Let $c,d\in\mathbb{Q}$ and let $H'=\mathbb{H}[\mathbb{Q},c,d]$ be the associated quaternion algebra over $\mathbb{Q}$ (generators $i,j$ with $i^2=c$, $j^2=d$, $ij=-ji$). Let $t,s,c'$ be nonzero rationals, and let $y,z\in H'$ satisfy $y^2=t$, $z^2=c'$ (as images of $t,c'$ under the structure map $\mathbb{Q}\to H'$), $yz=-zy$, and suppose every $u\in H'$ can be written $u=\alpha\cdot 1+\beta y+\gamma z+\delta\,(yz)$ with $\alpha,\beta,\gamma,\delta\in\mathbb{Q}$. The conclusion asserts the existence of a $\mathbb{Q}$-algebra homomorphism $\tau\colon \mathbb{H}[\mathbb{Q},t,sc']\to M_2(H')$ with three properties: $\tau$ is injective; it sends the two standard generators to $$\tau(i)=\begin{pmatrix} y&0\\ 0&y\end{pmatrix},\qquad \tau(j)=\begin{pmatrix} 0& s z\\ z&0\end{pmatrix};$$ and its image is exactly the joint commutant of the two matrices $X=\begin{pmatrix} y&0\\ 0&-y\end{pmatrix}$ and $W=\begin{pmatrix} 0& s\\ 1&0\end{pmatrix}$ (the entry $s$ being its image in $H'$), i.e. for all $Y\in M_2(H')$ one has $YX=XY$ and $YW=WY$ if and only if $Y$ lies in the range of $\tau$.
--
--   Here $X$ and $W$ are the images of standard generators $x,w$ with $x^2=t$, $w^2=s$, $xw=-wx$ of a quaternion algebra $B=(t,s)$ under an embedding $B\hookrightarrow M_2(H')$ coming from a shared quadratic subfield, so the statement identifies the centraliser of the embedded $B$ as the symbol algebra $(t,sc')$ over $\mathbb{Q}$, presented with explicit generators. It is used in the construction of such embeddings together with control of traces and commutants for indefinite quaternion algebras ramified at a prescribed set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute
    {c d : ℚ} (t s c' : ℚ) (ht : t ≠ 0) (hs : s ≠ 0) (hc' : c' ≠ 0)
    (y z : ℍ[ℚ, c, d]) (hy : y * y = algebraMap ℚ ℍ[ℚ, c, d] t) (hz : z * z = algebraMap ℚ ℍ[ℚ, c, d] c')
    (hyz : y * z = -(z * y))
    (hspan : ∀ u : ℍ[ℚ, c, d], ∃ α β γ δ : ℚ, u = α • 1 + β • y + γ • z + δ • (y * z)) :
    ∃ τ : ℍ[ℚ, t, s * c'] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d],
      Function.Injective τ ∧
      τ ⟨0, 1, 0, 0⟩ = !![y, 0; 0, y] ∧ τ ⟨0, 0, 1, 0⟩ = !![0, s • z; z, 0] ∧
      ∀ Y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d],
        (Y * !![y, 0; 0, -y] = !![y, 0; 0, -y] * Y ∧
            Y * !![0, algebraMap ℚ ℍ[ℚ, c, d] s; 1, 0] = !![0, algebraMap ℚ ℍ[ℚ, c, d] s; 1, 0] * Y) ↔
          Y ∈ Set.range τ := by sorry
