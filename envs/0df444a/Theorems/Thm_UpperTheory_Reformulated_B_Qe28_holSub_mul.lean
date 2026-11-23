-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qe28_holSub_mul
-- name    : UpperTheory.Reformulated.B.Qe28.holSub_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:36.509193+00:00
-- url     : https://prove2.me/theorems/634ccc95-4fb1-4484-a2df-270c95c3093c
-- title:
--   Qe28: hol Sub mul
-- statement:
--   The Qe28 construction uses the hol Sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HolSubMul.lean#L119-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HolSubMul.lean#L119-L482

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HolSubMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qe28.holSub_mul :
    ∀ {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
      [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat},
      @ReciprocityTheory.ChartRestriction.G.FD.SiegelSpaceAlgebra E inst inst_1 inst_2 →
        ∀ {Comp : Type} {X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r}
          {la la' : (k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r}
          {P Q : @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X},
          @Membership.mem (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
              (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                (@Pi.addCommMonoid Comp
                  (fun (c : Comp) ↦
                    @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                  fun (i : Comp) ↦
                  @Pi.addCommMonoid
                    (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                    (fun (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex)
                    fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                    Complex.instAddCommMonoid)
                (@Pi.module Comp
                  (fun (c : Comp) ↦
                    @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                  Complex Complex.instSemiring
                  (fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  fun (i : Comp) ↦
                  @Pi.Function.module
                    (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                    Complex Complex.instSemiring Complex.instAddCommMonoid
                    (@Semiring.toModule Complex Complex.instSemiring)))
              (@SetLike.instMembership
                (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring)))
                (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring))))
              (@UpperTheory.Reformulated.B.Qe28.holSub E inst inst_1 inst_2 r Comp X la) P →
            @Membership.mem (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring)))
                (@SetLike.instMembership
                  (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring)))
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring))))
                (@UpperTheory.Reformulated.B.Qe28.holSub E inst inst_1 inst_2 r Comp X la') Q →
              @Membership.mem (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring)))
                (@SetLike.instMembership
                  (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring)))
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring))))
                (@UpperTheory.Reformulated.B.Qe28.holSub E inst inst_1 inst_2 r Comp X
                  (@HAdd.hAdd
                    ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                    ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                    ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                    (@instHAdd
                      ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                      (@Pi.instAdd Comp
                        (fun (k : Comp) ↦
                          @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                        fun (i : Comp) ↦
                        @Pi.instAdd (↥(@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)))
                          (fun (a : ↥(@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))) ↦ Fin r → Int)
                          fun (i : ↥(@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))) ↦
                          @Pi.instAdd (Fin r) (fun (a : Fin r) ↦ Int) fun (i : Fin r) ↦ Int.instAdd))
                    la la'))
                (@HMul.hMul (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@instHMul (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                    (@Pi.instMul Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.instMul
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instMul))
                  P Q) := by sorry
