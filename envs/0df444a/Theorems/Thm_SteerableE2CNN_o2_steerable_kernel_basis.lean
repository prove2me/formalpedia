-- Prove2me | Theorems.Thm_SteerableE2CNN_o2_steerable_kernel_basis
-- name    : SteerableE2CNN.o2_steerable_kernel_basis
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:41:26.140154+00:00
-- url     : https://prove2.me/theorems/c5b95c2f-3f88-4b29-b49c-d13e3d2a6e2d
-- title:
--   Table 2 (as derived in Appendix F.4.3): the basis of $\mathrm{O}(2)$-steerable kernels
-- statement:
--   Let $\psi_{i,m}$ and $\psi_{j,n}$ be real irreps of $\mathrm{O}(2)$, where $i,j\in\{0,1\}$ and $m,n\in\mathbb{N}$, with $m=0$ or $i=1$ and with $n=0$ or $j=1$. They are $\psi_{i,0}(r_\theta s)=s^i$ and $\psi_{1,k}(r_\theta s)=\psi(k\theta)\xi(s)$ for $k\ge1$, and $r_\theta s$ acts on the plane by the matrix $\psi(\theta)\xi(s)$. Let $\{b_\beta\}$ be the angular functions derived in Appendix F.4.3, each of angular frequency $\mu_\beta$:
--
--   - $m=n=0$: $b(\phi)=[1]$ ($\mu=0$) if $i=j$, and no element if $i\neq j$ (eq. 35);
--   - $m=0<n$: $b(\phi)=[\cos(n\phi+i\tfrac{\pi}{2}),\ \sin(n\phi+i\tfrac{\pi}{2})]$, $\mu=n$ (eq. 38);
--   - $n=0<m$: $b(\phi)=[\cos(m\phi+j\tfrac{\pi}{2});\ \sin(m\phi+j\tfrac{\pi}{2})]$, $\mu=m$ (eq. 37);
--   - $m,n>0$: $b_s(\phi)=\psi(\mu\phi)\xi(s)$ with $\mu=m-sn$, $s\in\{\pm1\}$, i.e. $\psi((m-n)\phi)$ and $\psi((m+n)\phi)\xi(-1)$ (eq. 34).
--
--   Then:
--
--   1. A kernel $\kappa:\mathbb{R}^2\to\mathbb{R}^{\dim\psi_{i,m}\times\dim\psi_{j,n}}$ satisfies the irrep constraint
--
--   $$\kappa(gx)=\psi_{i,m}(g)\,\kappa(x)\,\psi_{j,n}(g)^{-1}\qquad\forall g=r_\theta s\in\mathrm{O}(2),\ x\in\mathbb{R}^2$$
--
--   if and only if there are radial functions $w_\beta$ with $\kappa(x(r,\phi))=\sum_\beta w_\beta(r)\,b_\beta(\phi)$ for all $r\ge0$ and $\phi$, and $w_\beta(0)=0$ whenever $\mu_\beta\neq0$.
--   2. The functions $b_\beta$ are linearly independent.
--
--   Combined with the irrep decomposition of Section 2.4, this gives a complete basis of $\mathrm{O}(2)$-steerable kernels between arbitrary field types. It is the kernel space used by $\mathrm{E}(2)$-steerable CNNs.
--
--   **Formalization Note** This is the statement as derived in Appendix F.4.3. Table 2 (and Table 9) lists, for the trivial-input or trivial-output cells mixing a one- and a two-dimensional irrep, the functions that eqs. (37), (38) derive for the sign-flip irrep, and the other way round. For example, $[\sin(n\phi),-\cos(n\phi)]$ violates the constraint for $\psi_{0,0}\leftarrow\psi_{1,n}$ at the reflection $s=-1$, $\theta=0$, while $[\cos(n\phi),\sin(n\phi)]$ satisfies it. The Lean statement uses the derived functions. The spans of the $1\times1$ and $2\times2$ cells agree with Table 2. Kernels are arbitrary functions with the constraint imposed at every point, and the radial coefficients are arbitrary functions. The group elements are parametrised as $r_\theta s$ with $\theta\in\mathbb{R}$ and $s\in\{\pm1\}$, which covers all of $\mathrm{O}(2)$.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Section 2.5, eq. (5) and Table 2, p. 5; Appendix F.3, Table 9, p. 29; Appendix F.4.3, eqs. (34), (35), (37), (38), pp. 40-43; Appendix F.4.6, p. 48

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

open Matrix MeasureTheory

namespace SteerableE2CNN

theorem o2_steerable_kernel_basis (l l' : O2IrrepLabel)
    (κ : Plane → Matrix (Fin (o2Dim l)) (Fin (o2Dim l')) ℝ) :
    (KernelConstraint (fun g : ℝ × ℤˣ => o2Elem g.1 g.2) (fun g => o2Irrep l g.1 g.2)
        (fun g => o2Irrep l' g.1 g.2) κ ↔
      ∃ w : Fin (o2BasisCard l l') → ℝ → ℝ,
        (∀ b, o2BasisFreq l l' b ≠ 0 → w b 0 = 0) ∧
        ∀ r : ℝ, 0 ≤ r → ∀ φ : ℝ, κ (polar r φ) = ∑ b, w b r • o2Basis l l' b φ) ∧
    LinearIndependent ℝ (o2Basis l l') := by sorry

end SteerableE2CNN
