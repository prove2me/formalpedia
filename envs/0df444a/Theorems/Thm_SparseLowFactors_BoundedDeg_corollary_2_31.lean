-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_corollary_2_31
-- name    : SparseLowFactors.BoundedDeg.corollary_2_31
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:24:38.839431+00:00
-- url     : https://prove2.me/theorems/b9250851-e28f-4872-bdf7-0c0c61d565b3
-- title:
--   Corollary 2.31 — the largest power of $X_i$ dividing a monomial multiple of a sparse factor, deterministically
-- statement:
--   Let $F$ be a field with $|F|\ge\mathrm{poly}(n,s,d)$ and $i\in[n]$. Let $f\in F[X_1,\dots,X_n]$ divide a non-zero $s$-sparse polynomial of individual degree at most $d$, and suppose $f$ is not divisible by a monomial. Let $\Gamma$ be an algebraic circuit of size $m$ computing a non-zero $g$ of degree at most $D$ with $f\prec_dg$. There is a deterministic algorithm that, given $\Gamma$, computes the largest $e$ with $X_i^e\mid g$ in time $\mathrm{poly}(n,s,d,D,m)$.
--
--   Formally: universal $C$ and a fixed program $P$ such that for every field $F$ that is infinite or has $|F|\ge C(n+s+d)^C$, all such data with $\Gamma$ of $N$ nodes and every $w\ge C\log_2(n+s+d+m+N+D+2)$, $P$ run on $(n,s,d,D,i)$ and the encoding of $\Gamma$ halts within $C(n+s+d+D+m+N)^C$ steps without calling `factor`, with $e=W[0]$ at halting satisfying $X_i^e\mid g$ and $X_i^{e+1}\nmid g$.
--
--   This is the first post-processing step of Algorithm 2, which strips the monomial $M$ from $h=gM$.
--
--   Differences from the source:
--   - encoding: "there is an algorithm that runs in time …" → one fixed program P for the deterministic algebraic RAM (Machine), chosen before the field and the instance; time = number of executed instructions; reason: the paper names no machine; unit-cost field operations are its stated convention (p. 15)
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - reading: "algebraic circuit of size m and degree D" → the circuit has size m and computes g with total degree ≤ D; reason: the weakest reading of "degree D"; a formal-degree bound implies it
--   - encoding: no univariate factoring → the program makes no `factor` call; reason: the printed time bound has no T(F, d) term
--   - encoding: "i ∈ [n]" → i : Fin n (indices from 0); reason: index convention
--   - encoding: given C; output the largest power → input (n, s, d, D, i) and the encoding of Γ; the exponent is read from W[0]; reason: input/output layout
--   - encoding: circuit of size m (number of wires) → the input circuit's node count N = Γ.numNodes joins the time bound (C·(n+s+d+D+m+N)^C) and the word-length bound (w ≥ C·log₂(n+s+d+m+N+D+2)); reason: a node not connected to the output adds no wire but still occupies input cells and needs a word-sized index (without N, two circuits whose node indices agree modulo 2^w have the same input memory and different values); a circuit all of whose nodes feed the output has N ≤ m + 1, where the bounds are the printed ones up to the universal constant
--   - encoding: word size not discussed → every word length w ≥ C·log₂(…); reason: indices and counters fit in a word, but words cannot encode field data
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 26, Corollary 2.31

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits
import Definitions.Def_SparseLowFactors_BoundedDeg_Machine

open SetMultCost MvPolynomial

namespace SparseLowFactors.BoundedDeg

theorem corollary_2_31 :
    ∃ C : ℕ, ∃ P : List Instr,
    ∀ (F : Type) [Field F] (n s d m D : ℕ) (i : Fin n),
      (Infinite F ∨ C * (n + s + d) ^ C ≤ Nat.card F) →
      ∀ w : ℕ,
      ∀ fac : FactorOracle F, ∀ e : ℕ → F, EnumOK e →
      ∀ f : MvPolynomial (Fin n) F,
        (∃ F₀ : MvPolynomial (Fin n) F, F₀ ≠ 0 ∧ IsSparse s F₀ ∧ IndDegLE d F₀ ∧ f ∣ F₀) →
        NoMonomialDivisor f →
      ∀ (Γ : Circuit (Fin n) F) (g : MvPolynomial (Fin n) F),
        Γ.size = m → g.totalDegree ≤ D → Γ.value = g → g ≠ 0 → PrecR d f g →
        C * Nat.log 2 (n + s + d + m + Γ.numNodes + D + 2) ≤ w →
      ∃ (T : ℕ) (res : Result F w),
        run P fac e T
          (loadWords w ([(n : ℤ), (s : ℤ), (d : ℤ), (D : ℤ), (i.val : ℤ)] ++
            circuitWords (fun j => j.val) Γ))
          (loadFields (circuitFields Γ)) = some res ∧
        T ≤ C * (n + s + d + D + m + Γ.numNodes) ^ C ∧
        res.facCalls = 0 ∧
        X i ^ (res.wm 0).toNat ∣ g ∧ ¬ X i ^ ((res.wm 0).toNat + 1) ∣ g := by sorry

end SparseLowFactors.BoundedDeg
