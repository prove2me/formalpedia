-- Prove2me | Theorems.Thm_RH_Transport_PhysicalHigh_source_batch_inverse_fields
-- name    : RH.Transport.PhysicalHigh.source_batch_inverse_fields
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T04:56:30.688038+00:00
-- url     : https://prove2.me/theorems/7653b52b-d32a-4776-8e34-4cf8049bbf93
-- title:
--   Inverse raw and inverse marked moment fields for $N$ distinct slots, with constant $C(1+h)^J$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$ and a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development. A *batch* at scale $U$ is the detector batch of that development: a finite set of free rows with a detector family, slot widths, slot profiles and external points, partitioned into fibers by a bin, a label and two index sets; for a fiber $F$ the exponents $F.r$ and $F.m$ are its inverse and plain length exponents and $\mathrm{poly}_F(u;\cdot)$ denotes the rowwise Dirichlet polynomial of the row $u$.
--
--   **Data.** Let $F_0$ be source data with excluded set $S$ and real window $w$, and let $\ell_1,\dots,\ell_N>0$ be slot lengths. The batches considered are those at scale $U=Z^{d}$ with $d\ge\tfrac1{200}$ whose row data is the source moment data of $\eta$ for $(M,H,S)$, whose slot profile is $w$ in every slot and whose slot widths are $\ell_s/d$. Here $M$ is an arbitrary nonzero ideal and $H\le(\mathcal O/M)^\times$ a subgroup containing the image of the global units; the slot lengths are pairwise distinct; the slot upper bound is $2$ and all external points have real part $\tfrac{17}{50}$. Let $\varepsilon_m>0$ and let $c_B,k_B,c_H,k_H>0$ be count parameters.
--
--   **Statement.** There is $J\in\mathbb N$ such that for every Hecke character $\eta$ there is $C>0$ for which, for all sufficiently large $Z$, one has $Z>1$ and, for every such batch, every nonempty fiber $F$ and every height $h\ge0$, both inverse moment fields hold with constant $C(1+h)^{J}$:
--
--   1. *(inverse raw)* for $n\le2$, $s\in[0,1]$ and $|t|\le h$, the raw moment bound holds for the row data of $F$ and for the twisted logarithmic test profile of order $n$, and for its rescaling, with count parameters $(c_B,k_B)$ if $2a-1\le\tfrac56$ and $(c_H,k_H)$ otherwise;
--
--   2. *(inverse marked)* for every set $\Sigma$ of slots of $F$ with $F.r+2\sum_{s\in\Sigma}w_s<1$ and $2F.r+8\sum_{s\in\Sigma}w_s<3$, and $n\le2$, $s\in[0,1]$, $|t|\le h$,
--   $$
--   \sum_{u\in F}\Big\lvert \mathrm{poly}^{\mathrm{inv}}_{F,n}(u;U^{F.r},s,t)\cdot\prod_{\sigma\in\Sigma}\mathrm{phys}_\sigma(u)\Big\rvert^{2}\le C(1+h)^{J}\,U^{1+\varepsilon_m}.
--   $$
--
--   These are the first two of the four moment fields of the detector. Compared with OpenAI's statement, the number of slots $N$ and the loss $\varepsilon_m$ are arguments and are not tied to the geometric data, and the constant is polynomial in the height with a degree fixed in advance.
--
--   **Formalization Note** The fields are stated for `B.fiber bin label left right hne` with `RawMoment`, `twistProfile`, `logTest`, `orientedProfile`, `scaleProfile`, `polynomial` and `physicalProduct` from OpenAI's detector modules. Distinctness of the slot lengths is `Function.Injective ell`. Relative to the source file, spaces were inserted after some `<` and `≤` signs and `open` commands for namespaces that contain no definitions were dropped, so that the statement elaborates against the platform's definition bundles; the statement is otherwise verbatim.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/InverseFields.lean, theorem source_batch_inverse_fields (L25-L50): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/InverseFields.lean#L25-L50

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_PhysicalHigh_PositiveFineSourceInput
set_option autoImplicit false

namespace RH.Transport.PhysicalHigh

noncomputable section

open scoped Classical BigOperators Topology
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance inverseFieldsQuotient:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance inverseFieldsLabels:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _


theorem source_batch_inverse_fields {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(N:ℕ)(ell:Fin N→ℝ)(hell:∀j,0< ell j)(hinj:Function.Injective ell)
    (εm:ℝ)(hεm:0< εm)
    (cB kB cH kH:ℝ)(hcB:0< cB)(hkB:0< kB)(hcH:0< cH)(hkH:0< kH):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ)≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=>ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then cB else cH)
        (if 2*a-1≤5/6 then kB else kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then cB else cH)
        (if 2*a-1≤5/6 then kB else kH) (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
          (C*(1+height)^J)*(Z^d)^(1+εm)) := by sorry

end
end RH.Transport.PhysicalHigh
