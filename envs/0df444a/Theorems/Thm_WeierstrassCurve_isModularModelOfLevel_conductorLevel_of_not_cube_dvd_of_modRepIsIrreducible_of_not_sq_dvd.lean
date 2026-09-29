-- Prove2me | Theorems.Thm_WeierstrassCurve_isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_not_sq_dvd
-- name    : WeierstrassCurve.isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/8ce89d75-00d4-5dd9-acff-4933f0381e1b
-- title:
--   Descent to the conductor level when p² ∤ N
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ which is a semistable model in the project's sense, i.e. for every prime $\ell$ with $\ell \mid W.\Delta$ one has $\ell \nmid W.c_4$ (`IsSemistableModel`). Let $N$ be a natural number and let $p$ be a prime (supplied as a `Fact` instance) with $p \neq 2$, and assume that the mod-$p$ representation of $W$ is irreducible in the project's sense: `ModRepIsIrreducible` unfolds to `GaloisRepIsIrreducible` for the action on the $p$-torsion points of $W$ base-changed along $\mathbb{Z} \to \mathbb{Q}$, taken over the algebraic closure of $\mathbb{Q}$. Assume further: $p^2 \nmid N$; $W$ is a modular model of level $N$, meaning (`IsModularModelOfLevel`) that there is a cusp form $f$ of weight $2$ on $\Gamma_0(N)$ which is a normalised eigenform and whose $q$-expansion coefficient at every prime $q$ that is a good prime for $W$ and does not divide $N$ equals $a_q(W)$, the trace of Frobenius computed from the model ($W.apOfModel\ q$); every prime $\ell$ dividing the discriminant $W.\Delta$ divides $N$; and no cube of a prime divides $N$. The conclusion is that $W$ is a modular model, in exactly the same sense, of level $W.conductorLevel$, which is defined to be the radical (product of distinct prime divisors) of $|W.\Delta|$ — in particular a squarefree level. Note that modularity here is only the matching of Hecke eigenvalues with $a_q(W)$ at good primes away from the level, not a statement about $L$-functions or about the curve rather than the chosen model.
--
--   This is the level-lowering step of the Frey–Serre–Ribet–Wiles route: starting from modularity at an auxiliary level $N$ that is divisible by the bad primes but is cube-free, one descends to the squarefree level given by the radical of the discriminant, which for a semistable model is the conductor. Compared with the textbook formulation (Ribet's theorem, and the removal of the auxiliary prime $p$ from the level), the formal statement is phrased entirely in terms of a normalised eigenform on $\Gamma_0$ whose prime coefficients agree with the $a_q$ of the given integral model at good primes away from the level, and it carries the extra hypothesis $p^2 \nmid N$, which is what makes the descent at $p$ elementary. It is the final descent used by the two modularity-lifting-at-conductor results for $p = 3$ and $p = 5$, which feed a residually modular semistable curve into the project's predicate [`Mlc1IsModularModelOfExactConductorLevel`](def/WeierstrassCurve_Mlc1RowStatement.html#L9).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_not_sq_dvd.lean

import Definitions.Def_WeierstrassCurve_ConductorLevel
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
WeierstrassCurve.isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_not_sq_dvd
    (W : WeierstrassCurve ℤ) (hss : W.IsSemistableModel) (N : ℕ)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hirr : W.ModRepIsIrreducible p)
    (hp2N : ¬ p ^ 2 ∣ N)
    (hN : W.IsModularModelOfLevel N) (hbad : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N)
    (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N) :
    W.IsModularModelOfLevel W.conductorLevel := by sorry
