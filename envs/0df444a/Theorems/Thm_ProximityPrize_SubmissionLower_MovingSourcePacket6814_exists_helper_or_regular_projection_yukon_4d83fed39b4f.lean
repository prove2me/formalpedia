-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourcePacket6814_exists_helper_or_regular_projection_yukon_4d83fed39b4f
-- name    : ProximityPrize.SubmissionLower.MovingSourcePacket6814.exists_helper_or_regular_projection_yukon_4d83fed39b4f
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-03T04:07:20.524465+00:00
-- url     : https://prove2.me/theorems/5a67d09c-60a1-482f-bd65-96eb591e289a
-- title:
--   ProximityPrize.SubmissionLower.MovingSourcePacket6814.exists_helper_or_regular_projection
-- statement:
--   No desired count, source dimension, faithful map, helper identity, or
--   projection-data supplier is assumed. This is the regular simple-quadratic
--   branch; its ownership/coverage hypotheses remain visible.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourcePacket6814.lean
--
--   yukon-proof-operation:certificate-b56-f100bba1a6f47cf654c2640503801a095b881040dd75a7091fffd7a3969d7444
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzM0OTgyMTQzZDMwNTYwZThjNmUxOTllMmE1NmIyNDE0OTcyOTFjNjJlNzA0YWM3YTliMjkyZjU4ODU4NGRiMyIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni1mMTAwYmJhMWE2ZjQ3Y2Y2NTRjMjY0MDUwMzgwMWEwOTViODgxMDQwZGQ3NWE3MDkxZmZmZDdhMzk2OWQ3NDQ0IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvbkxvd2VyLk1vdmluZ1NvdXJjZVBhY2tldDY4MTQuZXhpc3RzX2hlbHBlcl9vcl9yZWd1bGFyX3Byb2plY3Rpb25feXVrb25fNGQ4M2ZlZDM5YjRmIiwidiI6Mn0]

import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8



import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Log
import Init.Data.Vector.OfFn
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.List.FinRange
import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Batteries.Tactic.Lint
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Batteries.Control.Lemmas
import Mathlib.Data.Vector.Defs
import Batteries.Control.OptionT
import Batteries.Control.AlternativeMonad
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Mathlib.Order.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Set.Card
import Init.Data.Vector.Lemmas
import Mathlib.Control.Lawful
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Logic.Equiv.Sum
import Std.Tactic.Do
import Std.Internal.Do.Assertion
import Mathlib.Algebra.Order.Monoid.Defs
import Init.Data.String.Lemmas.Iterate
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Iterate
import Init.Data.String.Defs
import Init.Omega
import Init.Data.Slice.Lemmas
import Init.Data.Nat.Mod
import Init.Data.List.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Range
import Init.Data.Iterators.Lemmas
import Init.Data.Range
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Std.Do.Triple.SpecLemmas
import Init.Data.Slice.Array
import Init.Data.Range.Polymorphic
import Init.Data.Range.Polymorphic.Iterators
import Init.While
import Init.Syntax
import Lean.Meta.Sym.Pattern
import Lean.Meta.Tactic.Simp
import Lean.Meta.Match.MatcherApp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Do.Attr
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Sym.Apply
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Order
import Std.Data.HashMap.Lemmas
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Use
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Attr.Register
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Vector.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.AdjoinRoot
import Lean.Compiler.IR
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.ZMod
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.NormalClosure
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
import Mathlib.Order.GameAdd
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.GroupTheory.Submonoid.Inverses
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Real.Embedding
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Int.Associated
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.GradedMulAction
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.Flat.Localization
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_ba2ee1ab868a502d09acf5a7
import Definitions.Def_Yukon_ca06e00072579899a61b0098
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
import Definitions.Def_Yukon_a98065d48a835a5fe7279317
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
end MovingSourceGeometricBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MovingSourceCarrierField6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814
end WholeSpaceSourceAlternative6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
end WholeSpaceCubeUniform6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
end WholeSpaceCube6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN084
end RCN084
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN042
end RCN042
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN037
end RCN037
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN003
end RCN003
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourcePacket6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
open MvPolynomial RCN002 RCN003 RCN037 RCN042 RCN046 RCN084 RCN095 RCN135 RCN136 RCN234 RCN156 RCN264 RCN341
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierField6814 MovingSourceGeometricBudget6814
variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)

/-- No desired count, source dimension, faithful map, helper identity, or
projection-data supplier is assumed. This is the regular simple-quadratic
branch; its ownership/coverage hypotheses remain visible. -/
theorem exists_helper_or_regular_projection_yukon_4d83fed39b4f
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hJU : 9≤U) (hUT : U≤T) (hT : T≤1700)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (G : MvPolynomial (Fin 3) OmegaT) (hcarrier : G∣surfaceMap phi F)
    (hG : Irreducible G) (hproper : ¬G∣regularEquation F quadratic A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (p q : FlagDegree) (hp : PolynomialInFlag p G)
    (hq : PolynomialInFlag q (regularEquation F quadratic A))
    (hdeg : p.zOnly+p.yz+p.all<2130706433)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<2130706433) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ base : ∀ C : MovingFamily F G quadratic A, SeparableLiteralCoordinate C.1,
        Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩)  := by sorry
end
end MovingSourcePacket6814
end SubmissionLower
end ProximityPrize
